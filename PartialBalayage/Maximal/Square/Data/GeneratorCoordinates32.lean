/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorFastCubicValidity
public import PartialBalayage.Maximal.Square.ExactRationalLiteral

/-!
# Checked actual coordinate intervals and signed power lookup

These literals are proposed data. Every stated equality and bound is proved by
ordinary Lean kernel reduction against the actual coefficients and powers.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Actual coordinate interval candidates, block 32. -/
def generatorCoordinates32 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 7
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (4835367921667552423) 9830400000000000000000),
            (exactRationalLiteral (-439578901969777493) 102400000000000000000),
            (exactRationalLiteral (39961718360888863) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (13327852732575786773) 491520000000000000000),
            (exactRationalLiteral (-199224478429787399) 5120000000000000000),
            (exactRationalLiteral (-5432834878154899) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-50394033290005566651) 1638400000000000000000),
            (exactRationalLiteral (8256816997162872307) 51200000000000000000),
            (exactRationalLiteral (-378631689312993) 64000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-484095772588136805167) 9830400000000000000000),
            (exactRationalLiteral (-20026206124996732627) 102400000000000000000),
            (exactRationalLiteral (352956347895749017) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (677096452171919368967) 9830400000000000000000),
            (exactRationalLiteral (7830214614022715563) 102400000000000000000),
            (exactRationalLiteral (-93156015050808077) 640000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-11044697315141274569) 614400000000000000000),
            (exactRationalLiteral (31292207249024119) 6400000000000000000),
            (exactRationalLiteral (16157010942650311) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (5308464684837114797) 1638400000000000000000),
            (exactRationalLiteral (-193793155767648981) 51200000000000000000),
            (exactRationalLiteral (-37096359351898689) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1870079267947201933) 327680000000000000000),
            (exactRationalLiteral (145736542665116807) 51200000000000000000),
            (exactRationalLiteral (2173792959630207) 320000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (8528561321396384133) 819200000000000000000),
            (exactRationalLiteral (237847126012237787) 25600000000000000000),
            (exactRationalLiteral (1464902278210263) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-117113070285671795683) 4915200000000000000000),
            (exactRationalLiteral (-96808655459586203) 10240000000000000000),
            (exactRationalLiteral (2521338825681701) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-165533916866984077103) 9830400000000000000000),
            (exactRationalLiteral (-1954247215055257427) 102400000000000000000),
            (exactRationalLiteral (-49894217453963111) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (99709937991135643621) 4915200000000000000000),
            (exactRationalLiteral (1062703027291651489) 51200000000000000000),
            (exactRationalLiteral (14538358651426093) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-18080369682958487581) 9830400000000000000000),
            (exactRationalLiteral (-76058375877770069) 20480000000000000000),
            (exactRationalLiteral (2454270820931839) 640000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-2587538951649492713) 4915200000000000000000),
            (exactRationalLiteral (284964031297084331) 51200000000000000000),
            (exactRationalLiteral (-279430510267001) 64000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (9745898634303218903) 983040000000000000000),
            (exactRationalLiteral (-424201399589979161) 51200000000000000000),
            (exactRationalLiteral (4062097192732363) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (166950842192043786607) 4915200000000000000000),
            (exactRationalLiteral (-1005766530897520109) 51200000000000000000),
            (exactRationalLiteral (13886409753235111) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-200156578895898107417) 9830400000000000000000),
            (exactRationalLiteral (1866729798695828139) 102400000000000000000),
            (exactRationalLiteral (-33670801150010657) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-184966828768500780727) 9830400000000000000000),
            (exactRationalLiteral (729121359133958853) 102400000000000000000),
            (exactRationalLiteral (-2975455939512367) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12934435618634930449) 2457600000000000000000),
            (exactRationalLiteral (21951351275345971) 25600000000000000000),
            (exactRationalLiteral (1202156657955431) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-958197355422636811) 9830400000000000000),
            (exactRationalLiteral (597116359001023569) 12800000000000000000),
            (exactRationalLiteral (-6083013796065551) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1011683816497902097889) 4915200000000000000000),
            (exactRationalLiteral (-5242884648716337507) 51200000000000000000),
            (exactRationalLiteral (50613016781128553) 1600000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-958197355422636811) 9830400000000000000),
            (exactRationalLiteral (597116359001023569) 12800000000000000000),
            (exactRationalLiteral (-6083013796065551) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-12934435618634930449) 2457600000000000000000),
            (exactRationalLiteral (21951351275345971) 25600000000000000000),
            (exactRationalLiteral (1202156657955431) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-184966828768500780727) 9830400000000000000000),
            (exactRationalLiteral (729121359133958853) 102400000000000000000),
            (exactRationalLiteral (-2975455939512367) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-200156578895898107417) 9830400000000000000000),
            (exactRationalLiteral (1866729798695828139) 102400000000000000000),
            (exactRationalLiteral (-33670801150010657) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (166950842192043786607) 4915200000000000000000),
            (exactRationalLiteral (-1005766530897520109) 51200000000000000000),
            (exactRationalLiteral (13886409753235111) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (9745898634303218903) 983040000000000000000),
            (exactRationalLiteral (-424201399589979161) 51200000000000000000),
            (exactRationalLiteral (4062097192732363) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2587538951649492713) 4915200000000000000000),
            (exactRationalLiteral (284964031297084331) 51200000000000000000),
            (exactRationalLiteral (-279430510267001) 64000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-18080369682958487581) 9830400000000000000000),
            (exactRationalLiteral (-76058375877770069) 20480000000000000000),
            (exactRationalLiteral (2454270820931839) 640000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (99709937991135643621) 4915200000000000000000),
            (exactRationalLiteral (1062703027291651489) 51200000000000000000),
            (exactRationalLiteral (14538358651426093) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-165533916866984077103) 9830400000000000000000),
            (exactRationalLiteral (-1954247215055257427) 102400000000000000000),
            (exactRationalLiteral (-49894217453963111) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-117113070285671795683) 4915200000000000000000),
            (exactRationalLiteral (-96808655459586203) 10240000000000000000),
            (exactRationalLiteral (2521338825681701) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (8528561321396384133) 819200000000000000000),
            (exactRationalLiteral (237847126012237787) 25600000000000000000),
            (exactRationalLiteral (1464902278210263) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1870079267947201933) 327680000000000000000),
            (exactRationalLiteral (145736542665116807) 51200000000000000000),
            (exactRationalLiteral (2173792959630207) 320000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5308464684837114797) 1638400000000000000000),
            (exactRationalLiteral (-193793155767648981) 51200000000000000000),
            (exactRationalLiteral (-37096359351898689) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-11044697315141274569) 614400000000000000000),
            (exactRationalLiteral (31292207249024119) 6400000000000000000),
            (exactRationalLiteral (16157010942650311) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (677096452171919368967) 9830400000000000000000),
            (exactRationalLiteral (7830214614022715563) 102400000000000000000),
            (exactRationalLiteral (-93156015050808077) 640000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-484095772588136805167) 9830400000000000000000),
            (exactRationalLiteral (-20026206124996732627) 102400000000000000000),
            (exactRationalLiteral (352956347895749017) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-50394033290005566651) 1638400000000000000000),
            (exactRationalLiteral (8256816997162872307) 51200000000000000000),
            (exactRationalLiteral (-378631689312993) 64000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (13327852732575786773) 491520000000000000000),
            (exactRationalLiteral (-199224478429787399) 5120000000000000000),
            (exactRationalLiteral (-5432834878154899) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (4835367921667552423) 9830400000000000000000),
            (exactRationalLiteral (-439578901969777493) 102400000000000000000),
            (exactRationalLiteral (39961718360888863) 3200000000000000000),
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
          (exactRationalLiteral (67881787021837158497) 1228800000000000000000),
          (exactRationalLiteral (3495731889798526337) 49152000000000000000),
          (exactRationalLiteral (28883391504915457) 1600000000000000000),
          (exactRationalLiteral (85406108579412253) 25600000000000000000),
          (exactRationalLiteral (3565220701992487093) 614400000000000000000),
          (exactRationalLiteral (3287940841360785277) 307200000000000000000),
          (exactRationalLiteral (14819646767904630949) 614400000000000000000),
          (exactRationalLiteral (21443540181795749153) 1228800000000000000000),
          (exactRationalLiteral (12867739219246228883) 614400000000000000000),
          (exactRationalLiteral (2397837532227034979) 1228800000000000000000),
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
          (exactRationalLiteral (2397837532227034979) 1228800000000000000000),
          (exactRationalLiteral (12867739219246228883) 614400000000000000000),
          (exactRationalLiteral (21443540181795749153) 1228800000000000000000),
          (exactRationalLiteral (14819646767904630949) 614400000000000000000),
          (exactRationalLiteral (3287940841360785277) 307200000000000000000),
          (exactRationalLiteral (3565220701992487093) 614400000000000000000),
          (exactRationalLiteral (85406108579412253) 25600000000000000000),
          (exactRationalLiteral (28883391504915457) 1600000000000000000),
          (exactRationalLiteral (3495731889798526337) 49152000000000000000),
          (exactRationalLiteral (67881787021837158497) 1228800000000000000000),
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
      (31, 42),
      (31, 26),
      (31, 10),
      (30, 58),
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
      (27, 53)
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (882790687426908519) 3276800000000000000000),
            (exactRationalLiteral (-294263562475636173) 102400000000000000000),
            (exactRationalLiteral (32695951386181797) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (12075643303279079311) 491520000000000000000),
            (exactRationalLiteral (-43358017606493827) 1024000000000000000),
            (exactRationalLiteral (-3349969923185969) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-6796749167793653757) 327680000000000000000),
            (exactRationalLiteral (1624145753339170367) 10240000000000000000),
            (exactRationalLiteral (-58578323000685411) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-199842575735142769519) 3276800000000000000000),
            (exactRationalLiteral (-734779110177751379) 4096000000000000000),
            (exactRationalLiteral (475407837380725059) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (239380452108282053639) 3276800000000000000000),
            (exactRationalLiteral (5793582998926045619) 102400000000000000000),
            (exactRationalLiteral (-552535732294294587) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3551368156572736721) 204800000000000000000),
            (exactRationalLiteral (100397986328183343) 6400000000000000000),
            (exactRationalLiteral (18395878596929301) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (953171438651613851) 327680000000000000000),
            (exactRationalLiteral (-352132207129472973) 51200000000000000000),
            (exactRationalLiteral (-42073166329013307) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (29062116447513056041) 4915200000000000000000),
            (exactRationalLiteral (192252699225977839) 51200000000000000000),
            (exactRationalLiteral (12389113482279481) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (27029599002207387613) 2457600000000000000000),
            (exactRationalLiteral (243333462428221507) 25600000000000000000),
            (exactRationalLiteral (1278265929781597) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-39994459406913077699) 1638400000000000000000),
            (exactRationalLiteral (-472110090589220079) 51200000000000000000),
            (exactRationalLiteral (3445254528673767) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-59291324361865738351) 3276800000000000000000),
            (exactRationalLiteral (-2161745244288127899) 102400000000000000000),
            (exactRationalLiteral (-430838377299777) 25600000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (106262629298742303247) 4915200000000000000000),
            (exactRationalLiteral (1121862881917174649) 51200000000000000000),
            (exactRationalLiteral (15041568661335487) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-20201016702077429719) 9830400000000000000000),
            (exactRationalLiteral (-324282458991088769) 102400000000000000000),
            (exactRationalLiteral (15733356094221593) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-967597527928455067) 4915200000000000000000),
            (exactRationalLiteral (254014174779700211) 51200000000000000000),
            (exactRationalLiteral (-1697833100403407) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (46234467396474573337) 4915200000000000000000),
            (exactRationalLiteral (-407234282726266993) 51200000000000000000),
            (exactRationalLiteral (4421461239123721) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (161078591426174695693) 4915200000000000000000),
            (exactRationalLiteral (-952365140645975461) 51200000000000000000),
            (exactRationalLiteral (12814285372537213) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-63116204329284805081) 3276800000000000000000),
            (exactRationalLiteral (1737864958930211123) 102400000000000000000),
            (exactRationalLiteral (-30761618732797851) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-60209875708533970167) 3276800000000000000000),
            (exactRationalLiteral (716309015060542141) 102400000000000000000),
            (exactRationalLiteral (-3430716097195989) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4262934240514181521) 819200000000000000000),
            (exactRationalLiteral (26509432679590139) 25600000000000000000),
            (exactRationalLiteral (1076884044166653) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-38754557640141418423) 409600000000000000000),
            (exactRationalLiteral (573431563292757017) 12800000000000000000),
            (exactRationalLiteral (-230375362322709) 16000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (980823906643864155811) 4915200000000000000000),
            (exactRationalLiteral (-5045411663148553131) 51200000000000000000),
            (exactRationalLiteral (9624695200552727) 320000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-38754557640141418423) 409600000000000000000),
            (exactRationalLiteral (573431563292757017) 12800000000000000000),
            (exactRationalLiteral (-230375362322709) 16000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-4262934240514181521) 819200000000000000000),
            (exactRationalLiteral (26509432679590139) 25600000000000000000),
            (exactRationalLiteral (1076884044166653) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-60209875708533970167) 3276800000000000000000),
            (exactRationalLiteral (716309015060542141) 102400000000000000000),
            (exactRationalLiteral (-3430716097195989) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-63116204329284805081) 3276800000000000000000),
            (exactRationalLiteral (1737864958930211123) 102400000000000000000),
            (exactRationalLiteral (-30761618732797851) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (161078591426174695693) 4915200000000000000000),
            (exactRationalLiteral (-952365140645975461) 51200000000000000000),
            (exactRationalLiteral (12814285372537213) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (46234467396474573337) 4915200000000000000000),
            (exactRationalLiteral (-407234282726266993) 51200000000000000000),
            (exactRationalLiteral (4421461239123721) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-967597527928455067) 4915200000000000000000),
            (exactRationalLiteral (254014174779700211) 51200000000000000000),
            (exactRationalLiteral (-1697833100403407) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-20201016702077429719) 9830400000000000000000),
            (exactRationalLiteral (-324282458991088769) 102400000000000000000),
            (exactRationalLiteral (15733356094221593) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (106262629298742303247) 4915200000000000000000),
            (exactRationalLiteral (1121862881917174649) 51200000000000000000),
            (exactRationalLiteral (15041568661335487) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-59291324361865738351) 3276800000000000000000),
            (exactRationalLiteral (-2161745244288127899) 102400000000000000000),
            (exactRationalLiteral (-430838377299777) 25600000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-39994459406913077699) 1638400000000000000000),
            (exactRationalLiteral (-472110090589220079) 51200000000000000000),
            (exactRationalLiteral (3445254528673767) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (27029599002207387613) 2457600000000000000000),
            (exactRationalLiteral (243333462428221507) 25600000000000000000),
            (exactRationalLiteral (1278265929781597) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (29062116447513056041) 4915200000000000000000),
            (exactRationalLiteral (192252699225977839) 51200000000000000000),
            (exactRationalLiteral (12389113482279481) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (953171438651613851) 327680000000000000000),
            (exactRationalLiteral (-352132207129472973) 51200000000000000000),
            (exactRationalLiteral (-42073166329013307) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-3551368156572736721) 204800000000000000000),
            (exactRationalLiteral (100397986328183343) 6400000000000000000),
            (exactRationalLiteral (18395878596929301) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (239380452108282053639) 3276800000000000000000),
            (exactRationalLiteral (5793582998926045619) 102400000000000000000),
            (exactRationalLiteral (-552535732294294587) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-199842575735142769519) 3276800000000000000000),
            (exactRationalLiteral (-734779110177751379) 4096000000000000000),
            (exactRationalLiteral (475407837380725059) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6796749167793653757) 327680000000000000000),
            (exactRationalLiteral (1624145753339170367) 10240000000000000000),
            (exactRationalLiteral (-58578323000685411) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (12075643303279079311) 491520000000000000000),
            (exactRationalLiteral (-43358017606493827) 1024000000000000000),
            (exactRationalLiteral (-3349969923185969) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (882790687426908519) 3276800000000000000000),
            (exactRationalLiteral (-294263562475636173) 102400000000000000000),
            (exactRationalLiteral (32695951386181797) 3200000000000000000),
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
          (exactRationalLiteral (3632883487353533) 9830400000000000000),
          (exactRationalLiteral (529788426047060181) 20480000000000000000),
          (exactRationalLiteral (210774337534350813) 8192000000000000000),
          (exactRationalLiteral (1275681076585693357) 19200000000000000000),
          (exactRationalLiteral (1433244375578557201) 19200000000000000000),
          (exactRationalLiteral (1362653778342388973) 76800000000000000000),
          (exactRationalLiteral (634593212736006003) 204800000000000000000),
          (exactRationalLiteral (19320834609361909) 3200000000000000000),
          (exactRationalLiteral (9037545855829161) 800000000000000000),
          (exactRationalLiteral (1896701730797959) 76800000000000000),
          (exactRationalLiteral (360396002929303261) 19200000000000000000),
          (exactRationalLiteral (214206238780239821) 9600000000000000000),
          (exactRationalLiteral (41259634784713379) 19200000000000000000),
          (exactRationalLiteral (2923926412334893) 8192000000000000000),
          (exactRationalLiteral (237346274731737749) 24576000000000000000),
          (exactRationalLiteral (20496833220802572833) 614400000000000000000),
          (exactRationalLiteral (24331993414006506071) 1228800000000000000000),
          (exactRationalLiteral (4569715467224907077) 245760000000000000000),
          (exactRationalLiteral (1608129716392740079) 307200000000000000000),
          (exactRationalLiteral (14750175947168216051) 153600000000000000000),
          (exactRationalLiteral (41504406534654470357) 204800000000000000000),
          (exactRationalLiteral (14750175947168216051) 153600000000000000000),
          (exactRationalLiteral (1608129716392740079) 307200000000000000000),
          (exactRationalLiteral (4569715467224907077) 245760000000000000000),
          (exactRationalLiteral (24331993414006506071) 1228800000000000000000),
          (exactRationalLiteral (20496833220802572833) 614400000000000000000),
          (exactRationalLiteral (237346274731737749) 24576000000000000000),
          (exactRationalLiteral (2923926412334893) 8192000000000000000),
          (exactRationalLiteral (41259634784713379) 19200000000000000000),
          (exactRationalLiteral (214206238780239821) 9600000000000000000),
          (exactRationalLiteral (360396002929303261) 19200000000000000000),
          (exactRationalLiteral (1896701730797959) 76800000000000000),
          (exactRationalLiteral (9037545855829161) 800000000000000000),
          (exactRationalLiteral (19320834609361909) 3200000000000000000),
          (exactRationalLiteral (634593212736006003) 204800000000000000000),
          (exactRationalLiteral (1362653778342388973) 76800000000000000000),
          (exactRationalLiteral (1433244375578557201) 19200000000000000000),
          (exactRationalLiteral (1275681076585693357) 19200000000000000000),
          (exactRationalLiteral (210774337534350813) 8192000000000000000),
          (exactRationalLiteral (529788426047060181) 20480000000000000000),
          (exactRationalLiteral (3632883487353533) 9830400000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (31, 43),
      (31, 27),
      (31, 11),
      (30, 59),
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
      (27, 52)
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
            (exactRationalLiteral (1246079036162261819) 9830400000000000000000),
            (exactRationalLiteral (-178011290880323117) 102400000000000000000),
            (exactRationalLiteral (25430184411474731) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3581011531941969531) 163840000000000000000),
            (exactRationalLiteral (-226024237815275151) 5120000000000000000),
            (exactRationalLiteral (-1267104968217039) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-18042084971936454207) 1638400000000000000000),
            (exactRationalLiteral (7788190413157389019) 51200000000000000000),
            (exactRationalLiteral (-107690853768545997) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-703549893725582410531) 9830400000000000000000),
            (exactRationalLiteral (-3244588685190186431) 20480000000000000000),
            (exactRationalLiteral (597859326865701101) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (745925402902709882779) 9830400000000000000000),
            (exactRationalLiteral (3409928755668358867) 102400000000000000000),
            (exactRationalLiteral (-639291389334548789) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9822010537968842533) 614400000000000000000),
            (exactRationalLiteral (178459236024458527) 6400000000000000000),
            (exactRationalLiteral (20634746251208291) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (3886664371046917257) 1638400000000000000000),
            (exactRationalLiteral (-530378486399755437) 51200000000000000000),
            (exactRationalLiteral (-1881998932245117) 64000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (30370382599392790631) 4915200000000000000000),
            (exactRationalLiteral (48969890104670531) 10240000000000000000),
            (exactRationalLiteral (13909262166407927) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5700838484508076231) 491520000000000000000),
            (exactRationalLiteral (248073253450490563) 25600000000000000000),
            (exactRationalLiteral (1091629581352931) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-122771000047118500103) 4915200000000000000000),
            (exactRationalLiteral (-456481241068540879) 51200000000000000000),
            (exactRationalLiteral (4369170231665833) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-191506544436109684003) 9830400000000000000000),
            (exactRationalLiteral (-2385085592355034427) 102400000000000000000),
            (exactRationalLiteral (-57815376870981139) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (113176318254221014561) 4915200000000000000000),
            (exactRationalLiteral (236607115316467077) 10240000000000000000),
            (exactRationalLiteral (15544778671244881) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-175552505399480429) 78643200000000000000),
            (exactRationalLiteral (-254425030635077601) 102400000000000000000),
            (exactRationalLiteral (19195358083783991) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (149534641248057913) 1638400000000000000000),
            (exactRationalLiteral (217050707280948051) 51200000000000000000),
            (exactRationalLiteral (-1998513649471809) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (43845556691172021463) 4915200000000000000000),
            (exactRationalLiteral (-388829709676989393) 51200000000000000000),
            (exactRationalLiteral (4780825285515079) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (155513883509246497891) 4915200000000000000000),
            (exactRationalLiteral (-180650449583444481) 10240000000000000000),
            (exactRationalLiteral (2348432198367863) 320000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-179278925929397871493) 9830400000000000000000),
            (exactRationalLiteral (1620636848833445331) 102400000000000000000),
            (exactRationalLiteral (-5570487263117009) 640000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-176374762669035744011) 9830400000000000000000),
            (exactRationalLiteral (701675630356390941) 102400000000000000000),
            (exactRationalLiteral (-3885976254879611) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2523464921478031801) 491520000000000000000),
            (exactRationalLiteral (6113284725735839) 5120000000000000000),
            (exactRationalLiteral (7612891443023) 6400000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-112890901630412534563) 1228800000000000000000),
            (exactRationalLiteral (551041286536481769) 12800000000000000000),
            (exactRationalLiteral (-5435754320069899) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (317039653404630846991) 1638400000000000000000),
            (exactRationalLiteral (-4857896840694228427) 51200000000000000000),
            (exactRationalLiteral (45633935224398717) 1600000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-112890901630412534563) 1228800000000000000000),
            (exactRationalLiteral (551041286536481769) 12800000000000000000),
            (exactRationalLiteral (-5435754320069899) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-2523464921478031801) 491520000000000000000),
            (exactRationalLiteral (6113284725735839) 5120000000000000000),
            (exactRationalLiteral (7612891443023) 6400000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-176374762669035744011) 9830400000000000000000),
            (exactRationalLiteral (701675630356390941) 102400000000000000000),
            (exactRationalLiteral (-3885976254879611) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-179278925929397871493) 9830400000000000000000),
            (exactRationalLiteral (1620636848833445331) 102400000000000000000),
            (exactRationalLiteral (-5570487263117009) 640000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (155513883509246497891) 4915200000000000000000),
            (exactRationalLiteral (-180650449583444481) 10240000000000000000),
            (exactRationalLiteral (2348432198367863) 320000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (43845556691172021463) 4915200000000000000000),
            (exactRationalLiteral (-388829709676989393) 51200000000000000000),
            (exactRationalLiteral (4780825285515079) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (149534641248057913) 1638400000000000000000),
            (exactRationalLiteral (217050707280948051) 51200000000000000000),
            (exactRationalLiteral (-1998513649471809) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-175552505399480429) 78643200000000000000),
            (exactRationalLiteral (-254425030635077601) 102400000000000000000),
            (exactRationalLiteral (19195358083783991) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (113176318254221014561) 4915200000000000000000),
            (exactRationalLiteral (236607115316467077) 10240000000000000000),
            (exactRationalLiteral (15544778671244881) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-191506544436109684003) 9830400000000000000000),
            (exactRationalLiteral (-2385085592355034427) 102400000000000000000),
            (exactRationalLiteral (-57815376870981139) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-122771000047118500103) 4915200000000000000000),
            (exactRationalLiteral (-456481241068540879) 51200000000000000000),
            (exactRationalLiteral (4369170231665833) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5700838484508076231) 491520000000000000000),
            (exactRationalLiteral (248073253450490563) 25600000000000000000),
            (exactRationalLiteral (1091629581352931) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (30370382599392790631) 4915200000000000000000),
            (exactRationalLiteral (48969890104670531) 10240000000000000000),
            (exactRationalLiteral (13909262166407927) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3886664371046917257) 1638400000000000000000),
            (exactRationalLiteral (-530378486399755437) 51200000000000000000),
            (exactRationalLiteral (-1881998932245117) 64000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-9822010537968842533) 614400000000000000000),
            (exactRationalLiteral (178459236024458527) 6400000000000000000),
            (exactRationalLiteral (20634746251208291) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (745925402902709882779) 9830400000000000000000),
            (exactRationalLiteral (3409928755668358867) 102400000000000000000),
            (exactRationalLiteral (-639291389334548789) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-703549893725582410531) 9830400000000000000000),
            (exactRationalLiteral (-3244588685190186431) 20480000000000000000),
            (exactRationalLiteral (597859326865701101) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-18042084971936454207) 1638400000000000000000),
            (exactRationalLiteral (7788190413157389019) 51200000000000000000),
            (exactRationalLiteral (-107690853768545997) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (3581011531941969531) 163840000000000000000),
            (exactRationalLiteral (-226024237815275151) 5120000000000000000),
            (exactRationalLiteral (-1267104968217039) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (1246079036162261819) 9830400000000000000000),
            (exactRationalLiteral (-178011290880323117) 102400000000000000000),
            (exactRationalLiteral (25430184411474731) 3200000000000000000),
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
          (exactRationalLiteral (31265163344920650653) 409600000000000000000),
          (exactRationalLiteral (31424747382216299413) 409600000000000000000),
          (exactRationalLiteral (40221107191858331) 2400000000000000000),
          (exactRationalLiteral (8536762406191531) 3200000000000000000),
          (exactRationalLiteral (155737094059020683) 24576000000000000000),
          (exactRationalLiteral (3656449219182712163) 307200000000000000000),
          (exactRationalLiteral (5171953095907401217) 204800000000000000000),
          (exactRationalLiteral (8284884484735082717) 409600000000000000000),
          (exactRationalLiteral (14596538865623338757) 614400000000000000000),
          (exactRationalLiteral (2831002648949269157) 1228800000000000000000),
          (exactRationalLiteral (133628329934033719) 614400000000000000000),
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
          (exactRationalLiteral (133628329934033719) 614400000000000000000),
          (exactRationalLiteral (2831002648949269157) 1228800000000000000000),
          (exactRationalLiteral (14596538865623338757) 614400000000000000000),
          (exactRationalLiteral (8284884484735082717) 409600000000000000000),
          (exactRationalLiteral (5171953095907401217) 204800000000000000000),
          (exactRationalLiteral (3656449219182712163) 307200000000000000000),
          (exactRationalLiteral (155737094059020683) 24576000000000000000),
          (exactRationalLiteral (8536762406191531) 3200000000000000000),
          (exactRationalLiteral (40221107191858331) 2400000000000000000),
          (exactRationalLiteral (31424747382216299413) 409600000000000000000),
          (exactRationalLiteral (31265163344920650653) 409600000000000000000),
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
      (31, 44),
      (31, 28),
      (31, 12),
      (30, 60),
      (30, 44),
      (30, 28),
      (30, 12),
      (29, 60),
      (29, 44),
      (29, 28),
      (29, 12),
      (28, 60),
      (28, 44),
      (28, 28),
      (28, 12),
      (27, 60),
      (27, 44),
      (27, 28),
      (27, 12),
      (26, 60),
      (26, 44),
      (26, 28),
      (26, 12),
      (25, 60),
      (25, 44),
      (25, 28),
      (25, 12),
      (24, 60),
      (24, 44),
      (24, 28),
      (24, 12),
      (23, 60),
      (23, 44),
      (23, 28),
      (23, 19),
      (23, 35),
      (23, 51),
      (24, 3),
      (24, 19),
      (24, 35),
      (24, 51),
      (25, 3),
      (25, 19),
      (25, 35),
      (25, 51),
      (26, 3),
      (26, 19),
      (26, 35),
      (26, 51),
      (27, 3),
      (27, 19),
      (27, 35),
      (27, 51)
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
        lower := (exactRationalLiteral (13) 16)
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
            (exactRationalLiteral (3632883487353533) 78643200000000000000),
            (exactRationalLiteral (-3632883487353533) 4096000000000000000),
            (exactRationalLiteral (3632883487353533) 640000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9380015369135528939) 491520000000000000000),
            (exactRationalLiteral (-226926927778205447) 5120000000000000000),
            (exactRationalLiteral (815759986751891) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-592390187010601521) 327680000000000000000),
            (exactRationalLiteral (7259201936547483859) 51200000000000000000),
            (exactRationalLiteral (-156803384536406583) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-793223436400959686081) 9830400000000000000000),
            (exactRationalLiteral (-13586603139518175667) 102400000000000000000),
            (exactRationalLiteral (720310816350677143) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (151673291227308886741) 1966080000000000000000),
            (exactRationalLiteral (679251884249655307) 102400000000000000000),
            (exactRationalLiteral (-726047046374802991) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8494682696190475919) 614400000000000000000),
            (exactRationalLiteral (265475956337849671) 6400000000000000000),
            (exactRationalLiteral (22873613905487281) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (2631071762386741859) 1638400000000000000000),
            (exactRationalLiteral (-728531993578496373) 51200000000000000000),
            (exactRationalLiteral (-52026780283242543) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (10670823681088771823) 1638400000000000000000),
            (exactRationalLiteral (60705359311448251) 10240000000000000000),
            (exactRationalLiteral (15429410850536373) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (10001661650941948347) 819200000000000000000),
            (exactRationalLiteral (50413299815808991) 5120000000000000000),
            (exactRationalLiteral (180998646584853) 160000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-125453761787937787117) 4915200000000000000000),
            (exactRationalLiteral (-87431345747178683) 10240000000000000000),
            (exactRationalLiteral (5293085934657899) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-206526684831525700289) 9830400000000000000000),
            (exactRationalLiteral (-2624268259255977011) 102400000000000000000),
            (exactRationalLiteral (-61775956579490153) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (120463081897809603019) 4915200000000000000000),
            (exactRationalLiteral (1246221111287133697) 51200000000000000000),
            (exactRationalLiteral (641919547246171) 64000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-23226421053781861747) 9830400000000000000000),
            (exactRationalLiteral (-170719594320816841) 102400000000000000000),
            (exactRationalLiteral (22657360073346389) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (324996747496037093) 983040000000000000000),
            (exactRationalLiteral (174073628800827851) 51200000000000000000),
            (exactRationalLiteral (-2299194198540211) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (8314277158544366297) 983040000000000000000),
            (exactRationalLiteral (-368987680442146361) 51200000000000000000),
            (exactRationalLiteral (5140189331906437) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (150230987456122443649) 4915200000000000000000),
            (exactRationalLiteral (-858427852711260941) 51200000000000000000),
            (exactRationalLiteral (10670036611141417) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-169877697342515368823) 9830400000000000000000),
            (exactRationalLiteral (1515045468405530763) 102400000000000000000),
            (exactRationalLiteral (-24943253898372239) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-34442632328517337637) 1966080000000000000000),
            (exactRationalLiteral (685221205021505253) 102400000000000000000),
            (exactRationalLiteral (-4341236412563233) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12423007818908704447) 2457600000000000000000),
            (exactRationalLiteral (34122324122613139) 25600000000000000000),
            (exactRationalLiteral (826338816589097) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-109648588444082491433) 1228800000000000000000),
            (exactRationalLiteral (21197821149287913) 512000000000000000),
            (exactRationalLiteral (-5112124582072073) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (922509228229306495343) 4915200000000000000000),
            (exactRationalLiteral (-936068036270672679) 10240000000000000000),
            (exactRationalLiteral (43144394446033799) 1600000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-109648588444082491433) 1228800000000000000000),
            (exactRationalLiteral (21197821149287913) 512000000000000000),
            (exactRationalLiteral (-5112124582072073) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-12423007818908704447) 2457600000000000000000),
            (exactRationalLiteral (34122324122613139) 25600000000000000000),
            (exactRationalLiteral (826338816589097) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-34442632328517337637) 1966080000000000000000),
            (exactRationalLiteral (685221205021505253) 102400000000000000000),
            (exactRationalLiteral (-4341236412563233) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-169877697342515368823) 9830400000000000000000),
            (exactRationalLiteral (1515045468405530763) 102400000000000000000),
            (exactRationalLiteral (-24943253898372239) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (150230987456122443649) 4915200000000000000000),
            (exactRationalLiteral (-858427852711260941) 51200000000000000000),
            (exactRationalLiteral (10670036611141417) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (8314277158544366297) 983040000000000000000),
            (exactRationalLiteral (-368987680442146361) 51200000000000000000),
            (exactRationalLiteral (5140189331906437) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (324996747496037093) 983040000000000000000),
            (exactRationalLiteral (174073628800827851) 51200000000000000000),
            (exactRationalLiteral (-2299194198540211) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-23226421053781861747) 9830400000000000000000),
            (exactRationalLiteral (-170719594320816841) 102400000000000000000),
            (exactRationalLiteral (22657360073346389) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (120463081897809603019) 4915200000000000000000),
            (exactRationalLiteral (1246221111287133697) 51200000000000000000),
            (exactRationalLiteral (641919547246171) 64000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-206526684831525700289) 9830400000000000000000),
            (exactRationalLiteral (-2624268259255977011) 102400000000000000000),
            (exactRationalLiteral (-61775956579490153) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-125453761787937787117) 4915200000000000000000),
            (exactRationalLiteral (-87431345747178683) 10240000000000000000),
            (exactRationalLiteral (5293085934657899) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (10001661650941948347) 819200000000000000000),
            (exactRationalLiteral (50413299815808991) 5120000000000000000),
            (exactRationalLiteral (180998646584853) 160000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (10670823681088771823) 1638400000000000000000),
            (exactRationalLiteral (60705359311448251) 10240000000000000000),
            (exactRationalLiteral (15429410850536373) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2631071762386741859) 1638400000000000000000),
            (exactRationalLiteral (-728531993578496373) 51200000000000000000),
            (exactRationalLiteral (-52026780283242543) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-8494682696190475919) 614400000000000000000),
            (exactRationalLiteral (265475956337849671) 6400000000000000000),
            (exactRationalLiteral (22873613905487281) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (151673291227308886741) 1966080000000000000000),
            (exactRationalLiteral (679251884249655307) 102400000000000000000),
            (exactRationalLiteral (-726047046374802991) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-793223436400959686081) 9830400000000000000000),
            (exactRationalLiteral (-13586603139518175667) 102400000000000000000),
            (exactRationalLiteral (720310816350677143) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-592390187010601521) 327680000000000000000),
            (exactRationalLiteral (7259201936547483859) 51200000000000000000),
            (exactRationalLiteral (-156803384536406583) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (9380015369135528939) 491520000000000000000),
            (exactRationalLiteral (-226926927778205447) 5120000000000000000),
            (exactRationalLiteral (815759986751891) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (3632883487353533) 78643200000000000000),
            (exactRationalLiteral (-3632883487353533) 4096000000000000000),
            (exactRationalLiteral (3632883487353533) 640000000000000000),
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
          (exactRationalLiteral (32695951386181797) 409600000000000000000),
          (exactRationalLiteral (1257775249994114561) 61440000000000000000),
          (exactRationalLiteral (1296221354292781827) 204800000000000000000),
          (exactRationalLiteral (12996266994151870213) 153600000000000000000),
          (exactRationalLiteral (23744222902990281847) 307200000000000000000),
          (exactRationalLiteral (384317048221445941) 25600000000000000000),
          (exactRationalLiteral (413550805438939349) 204800000000000000000),
          (exactRationalLiteral (515157808434870509) 76800000000000000000),
          (exactRationalLiteral (480684470493555287) 38400000000000000000),
          (exactRationalLiteral (1980451418101406213) 76800000000000000000),
          (exactRationalLiteral (3352918715138849317) 153600000000000000000),
          (exactRationalLiteral (1941408450042490963) 76800000000000000000),
          (exactRationalLiteral (369826199305148311) 153600000000000000000),
          (exactRationalLiteral (10999817757978619) 25600000000000000000),
          (exactRationalLiteral (213467948600103971) 24576000000000000000),
          (exactRationalLiteral (19104852148284999959) 614400000000000000000),
          (exactRationalLiteral (7270796587526486843) 409600000000000000000),
          (exactRationalLiteral (7261734222367085493) 409600000000000000000),
          (exactRationalLiteral (521784714104995091) 102400000000000000000),
          (exactRationalLiteral (927116026824119167) 10240000000000000000),
          (exactRationalLiteral (117085115840886733673) 614400000000000000000),
          (exactRationalLiteral (927116026824119167) 10240000000000000000),
          (exactRationalLiteral (521784714104995091) 102400000000000000000),
          (exactRationalLiteral (7261734222367085493) 409600000000000000000),
          (exactRationalLiteral (7270796587526486843) 409600000000000000000),
          (exactRationalLiteral (19104852148284999959) 614400000000000000000),
          (exactRationalLiteral (213467948600103971) 24576000000000000000),
          (exactRationalLiteral (10999817757978619) 25600000000000000000),
          (exactRationalLiteral (369826199305148311) 153600000000000000000),
          (exactRationalLiteral (1941408450042490963) 76800000000000000000),
          (exactRationalLiteral (3352918715138849317) 153600000000000000000),
          (exactRationalLiteral (1980451418101406213) 76800000000000000000),
          (exactRationalLiteral (480684470493555287) 38400000000000000000),
          (exactRationalLiteral (515157808434870509) 76800000000000000000),
          (exactRationalLiteral (413550805438939349) 204800000000000000000),
          (exactRationalLiteral (384317048221445941) 25600000000000000000),
          (exactRationalLiteral (23744222902990281847) 307200000000000000000),
          (exactRationalLiteral (12996266994151870213) 153600000000000000000),
          (exactRationalLiteral (1296221354292781827) 204800000000000000000),
          (exactRationalLiteral (1257775249994114561) 61440000000000000000),
          (exactRationalLiteral (32695951386181797) 409600000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (31, 45),
      (31, 29),
      (31, 13),
      (30, 61),
      (30, 45),
      (30, 29),
      (30, 13),
      (29, 61),
      (29, 45),
      (29, 29),
      (29, 13),
      (28, 61),
      (28, 45),
      (28, 29),
      (28, 13),
      (27, 61),
      (27, 45),
      (27, 29),
      (27, 13),
      (26, 61),
      (26, 45),
      (26, 29),
      (26, 13),
      (25, 61),
      (25, 45),
      (25, 29),
      (25, 13),
      (24, 61),
      (24, 45),
      (24, 29),
      (24, 13),
      (23, 61),
      (23, 45),
      (23, 29),
      (23, 18),
      (23, 34),
      (23, 50),
      (24, 2),
      (24, 18),
      (24, 34),
      (24, 50),
      (25, 2),
      (25, 18),
      (25, 34),
      (25, 50),
      (26, 2),
      (26, 18),
      (26, 34),
      (26, 50),
      (27, 2),
      (27, 18),
      (27, 34),
      (27, 50)
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
            (exactRationalLiteral (32695951386181797) 3276800000000000000000),
            (exactRationalLiteral (-32695951386181797) 102400000000000000000),
            (exactRationalLiteral (10898650462060599) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8036574382127194669) 491520000000000000000),
            (exactRationalLiteral (-219498157921260023) 5120000000000000000),
            (exactRationalLiteral (2898624941720821) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (10863756025539186333) 1638400000000000000000),
            (exactRationalLiteral (1306752667373227271) 10240000000000000000),
            (exactRationalLiteral (-205915915304267169) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-288536506494640236733) 3276800000000000000000),
            (exactRationalLiteral (-10460456895145515011) 102400000000000000000),
            (exactRationalLiteral (168552461167130637) 640000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (251127460085794570949) 3276800000000000000000),
            (exactRationalLiteral (-2398447615330065061) 102400000000000000000),
            (exactRationalLiteral (-812802703415057193) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2206129373560138187) 204800000000000000000),
            (exactRationalLiteral (14457925890734271) 256000000000000000),
            (exactRationalLiteral (25112481559766271) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (959264911460626117) 1638400000000000000000),
            (exactRationalLiteral (-946592728665695781) 51200000000000000000),
            (exactRationalLiteral (-57003587260357161) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (34024865347552713259) 4915200000000000000000),
            (exactRationalLiteral (368284737327643639) 51200000000000000000),
            (exactRationalLiteral (16949559534664819) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (31527497320701491287) 2457600000000000000000),
            (exactRationalLiteral (255313199313884683) 25600000000000000000),
            (exactRationalLiteral (718356884495599) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-8533965964421685637) 327680000000000000000),
            (exactRationalLiteral (-414136553591277687) 51200000000000000000),
            (exactRationalLiteral (1243400327529993) 320000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-74343149394949826749) 3276800000000000000000),
            (exactRationalLiteral (-2879293244990955651) 102400000000000000000),
            (exactRationalLiteral (-65736536287999167) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (128134997269745894077) 4915200000000000000000),
            (exactRationalLiteral (262283897206313917) 10240000000000000000),
            (exactRationalLiteral (16551198691063669) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-23965002290868356533) 9830400000000000000000),
            (exactRationalLiteral (-73166150048306489) 102400000000000000000),
            (exactRationalLiteral (26119362062908787) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2525460247391371871) 4915200000000000000000),
            (exactRationalLiteral (125082939339339611) 51200000000000000000),
            (exactRationalLiteral (-2599874747608613) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (7884115887647479199) 983040000000000000000),
            (exactRationalLiteral (-347708195021737897) 51200000000000000000),
            (exactRationalLiteral (1099910675659559) 320000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (29040834456333156683) 983040000000000000000),
            (exactRationalLiteral (-817891955028091069) 51200000000000000000),
            (exactRationalLiteral (9597912230443519) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-53691702283064599963) 3276800000000000000000),
            (exactRationalLiteral (1421090817646467419) 102400000000000000000),
            (exactRationalLiteral (-22034071481159433) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-56051916763346383317) 3276800000000000000000),
            (exactRationalLiteral (666945739055885077) 102400000000000000000),
            (exactRationalLiteral (-959299314049371) 640000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4069619632943037187) 819200000000000000000),
            (exactRationalLiteral (37177134161391971) 25600000000000000000),
            (exactRationalLiteral (701066202800319) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-7101931083181478537) 81920000000000000000),
            (exactRationalLiteral (102028857975981037) 2560000000000000000),
            (exactRationalLiteral (-4788494844074247) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (894934961711425260889) 4915200000000000000000),
            (exactRationalLiteral (-902548337025191607) 10240000000000000000),
            (exactRationalLiteral (40654853667668881) 1600000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7101931083181478537) 81920000000000000000),
            (exactRationalLiteral (102028857975981037) 2560000000000000000),
            (exactRationalLiteral (-4788494844074247) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-4069619632943037187) 819200000000000000000),
            (exactRationalLiteral (37177134161391971) 25600000000000000000),
            (exactRationalLiteral (701066202800319) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-56051916763346383317) 3276800000000000000000),
            (exactRationalLiteral (666945739055885077) 102400000000000000000),
            (exactRationalLiteral (-959299314049371) 640000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-53691702283064599963) 3276800000000000000000),
            (exactRationalLiteral (1421090817646467419) 102400000000000000000),
            (exactRationalLiteral (-22034071481159433) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (29040834456333156683) 983040000000000000000),
            (exactRationalLiteral (-817891955028091069) 51200000000000000000),
            (exactRationalLiteral (9597912230443519) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (7884115887647479199) 983040000000000000000),
            (exactRationalLiteral (-347708195021737897) 51200000000000000000),
            (exactRationalLiteral (1099910675659559) 320000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2525460247391371871) 4915200000000000000000),
            (exactRationalLiteral (125082939339339611) 51200000000000000000),
            (exactRationalLiteral (-2599874747608613) 320000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-23965002290868356533) 9830400000000000000000),
            (exactRationalLiteral (-73166150048306489) 102400000000000000000),
            (exactRationalLiteral (26119362062908787) 3200000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (128134997269745894077) 4915200000000000000000),
            (exactRationalLiteral (262283897206313917) 10240000000000000000),
            (exactRationalLiteral (16551198691063669) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-74343149394949826749) 3276800000000000000000),
            (exactRationalLiteral (-2879293244990955651) 102400000000000000000),
            (exactRationalLiteral (-65736536287999167) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8533965964421685637) 327680000000000000000),
            (exactRationalLiteral (-414136553591277687) 51200000000000000000),
            (exactRationalLiteral (1243400327529993) 320000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (31527497320701491287) 2457600000000000000000),
            (exactRationalLiteral (255313199313884683) 25600000000000000000),
            (exactRationalLiteral (718356884495599) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (34024865347552713259) 4915200000000000000000),
            (exactRationalLiteral (368284737327643639) 51200000000000000000),
            (exactRationalLiteral (16949559534664819) 1600000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (959264911460626117) 1638400000000000000000),
            (exactRationalLiteral (-946592728665695781) 51200000000000000000),
            (exactRationalLiteral (-57003587260357161) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2206129373560138187) 204800000000000000000),
            (exactRationalLiteral (14457925890734271) 256000000000000000),
            (exactRationalLiteral (25112481559766271) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (251127460085794570949) 3276800000000000000000),
            (exactRationalLiteral (-2398447615330065061) 102400000000000000000),
            (exactRationalLiteral (-812802703415057193) 3200000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-288536506494640236733) 3276800000000000000000),
            (exactRationalLiteral (-10460456895145515011) 102400000000000000000),
            (exactRationalLiteral (168552461167130637) 640000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (10863756025539186333) 1638400000000000000000),
            (exactRationalLiteral (1306752667373227271) 10240000000000000000),
            (exactRationalLiteral (-205915915304267169) 1600000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (8036574382127194669) 491520000000000000000),
            (exactRationalLiteral (-219498157921260023) 5120000000000000000),
            (exactRationalLiteral (2898624941720821) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (32695951386181797) 3276800000000000000000),
            (exactRationalLiteral (-32695951386181797) 102400000000000000000),
            (exactRationalLiteral (10898650462060599) 3200000000000000000),
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
          (exactRationalLiteral (2147927253163301511) 204800000000000000000),
          (exactRationalLiteral (111800172188388475957) 1228800000000000000000),
          (exactRationalLiteral (11846604575338263493) 153600000000000000000),
          (exactRationalLiteral (14899442483658839) 1200000000000000000),
          (exactRationalLiteral (5780261002173387) 5120000000000000000),
          (exactRationalLiteral (1465888679686737619) 204800000000000000000),
          (exactRationalLiteral (53825831118537363) 4096000000000000000),
          (exactRationalLiteral (16154098270541833961) 614400000000000000000),
          (exactRationalLiteral (28983314727317574901) 1228800000000000000000),
          (exactRationalLiteral (16514895116114843567) 614400000000000000000),
          (exactRationalLiteral (602610291345744211) 245760000000000000000),
          (exactRationalLiteral (357619905352823813) 614400000000000000000),
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
          (exactRationalLiteral (357619905352823813) 614400000000000000000),
          (exactRationalLiteral (602610291345744211) 245760000000000000000),
          (exactRationalLiteral (16514895116114843567) 614400000000000000000),
          (exactRationalLiteral (28983314727317574901) 1228800000000000000000),
          (exactRationalLiteral (16154098270541833961) 614400000000000000000),
          (exactRationalLiteral (53825831118537363) 4096000000000000000),
          (exactRationalLiteral (1465888679686737619) 204800000000000000000),
          (exactRationalLiteral (5780261002173387) 5120000000000000000),
          (exactRationalLiteral (14899442483658839) 1200000000000000000),
          (exactRationalLiteral (11846604575338263493) 153600000000000000000),
          (exactRationalLiteral (111800172188388475957) 1228800000000000000000),
          (exactRationalLiteral (2147927253163301511) 204800000000000000000),
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
      (31, 46),
      (31, 30),
      (31, 14),
      (30, 62),
      (30, 46),
      (30, 30),
      (30, 14),
      (29, 62),
      (29, 46),
      (29, 30),
      (29, 14),
      (28, 62),
      (28, 46),
      (28, 30),
      (28, 14),
      (27, 62),
      (27, 46),
      (27, 30),
      (27, 14),
      (26, 62),
      (26, 46),
      (26, 30),
      (26, 14),
      (25, 62),
      (25, 46),
      (25, 30),
      (25, 14),
      (24, 62),
      (24, 46),
      (24, 30),
      (24, 14),
      (23, 62),
      (23, 46),
      (23, 30),
      (23, 17),
      (23, 33),
      (23, 49),
      (24, 1),
      (24, 17),
      (24, 33),
      (24, 49),
      (25, 1),
      (25, 17),
      (25, 33),
      (25, 49),
      (26, 1),
      (26, 17),
      (26, 33),
      (26, 49),
      (27, 1),
      (27, 17),
      (27, 33),
      (27, 49)
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (3632883487353533) 9830400000000000000000),
            (exactRationalLiteral (-3632883487353533) 102400000000000000000),
            (exactRationalLiteral (3632883487353533) 3200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2254233464573386701) 163840000000000000000),
            (exactRationalLiteral (-203737928244438879) 5120000000000000000),
            (exactRationalLiteral (4981489896689751) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (23042135663697242919) 1638400000000000000000),
            (exactRationalLiteral (5611874614113346507) 51200000000000000000),
            (exactRationalLiteral (-51005689214425551) 320000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-917769307226826057877) 9830400000000000000000),
            (exactRationalLiteral (-6844504692832950187) 102400000000000000000),
            (exactRationalLiteral (965213795320629227) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (728891039496261619357) 9830400000000000000000),
            (exactRationalLiteral (-5823169743070802237) 102400000000000000000),
            (exactRationalLiteral (-179911672091062279) 640000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4139393987735962699) 614400000000000000000),
            (exactRationalLiteral (466375808815979839) 6400000000000000000),
            (exactRationalLiteral (27351349214045261) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (-1168570637548346913) 1638400000000000000000),
            (exactRationalLiteral (-1184560691661353661) 51200000000000000000),
            (exactRationalLiteral (-61980394237471779) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (7288809816134213341) 983040000000000000000),
            (exactRationalLiteral (439123272834559807) 51200000000000000000),
            (exactRationalLiteral (3693941643758653) 320000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (33067250253805031909) 2457600000000000000000),
            (exactRationalLiteral (257813354155009747) 25600000000000000000),
            (exactRationalLiteral (531720536066933) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-130416009105409182833) 4915200000000000000000),
            (exactRationalLiteral (-77484143126938739) 10240000000000000000),
            (exactRationalLiteral (7140917340642031) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-241109888409085240213) 9830400000000000000000),
            (exactRationalLiteral (-3150160549559970347) 102400000000000000000),
            (exactRationalLiteral (-69697115996508181) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (136204141410267713191) 4915200000000000000000),
            (exactRationalLiteral (1378630700815643049) 51200000000000000000),
            (exactRationalLiteral (17054408700973063) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-24076718838445040431) 9830400000000000000000),
            (exactRationalLiteral (7647060436490691) 20480000000000000000),
            (exactRationalLiteral (5916272810494237) 640000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1037983929196508239) 1638400000000000000000),
            (exactRationalLiteral (70078638896483331) 51200000000000000000),
            (exactRationalLiteral (-580111059335403) 64000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (7480352472966421517) 983040000000000000000),
            (exactRationalLiteral (-324991253415764001) 51200000000000000000),
            (exactRationalLiteral (5858917424689153) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (140407707000739767637) 4915200000000000000000),
            (exactRationalLiteral (-781644554867712789) 51200000000000000000),
            (exactRationalLiteral (8525787849745621) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-152801334071420057347) 9830400000000000000000),
            (exactRationalLiteral (1338772896556255299) 102400000000000000000),
            (exactRationalLiteral (-19124889063946627) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-164213454855177536237) 9830400000000000000000),
            (exactRationalLiteral (646849232459530413) 102400000000000000000),
            (exactRationalLiteral (-5251756727930477) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-11977884389882311019) 2457600000000000000000),
            (exactRationalLiteral (39730853745015691) 25600000000000000000),
            (exactRationalLiteral (575793589011541) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-20704853585523929321) 245760000000000000000),
            (exactRationalLiteral (491637569979603849) 12800000000000000000),
            (exactRationalLiteral (-4464865106076421) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (289445470560522693193) 1638400000000000000000),
            (exactRationalLiteral (-4355101352012012347) 51200000000000000000),
            (exactRationalLiteral (38165312889303963) 1600000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20704853585523929321) 245760000000000000000),
            (exactRationalLiteral (491637569979603849) 12800000000000000000),
            (exactRationalLiteral (-4464865106076421) 400000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-11977884389882311019) 2457600000000000000000),
            (exactRationalLiteral (39730853745015691) 25600000000000000000),
            (exactRationalLiteral (575793589011541) 800000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-164213454855177536237) 9830400000000000000000),
            (exactRationalLiteral (646849232459530413) 102400000000000000000),
            (exactRationalLiteral (-5251756727930477) 3200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-152801334071420057347) 9830400000000000000000),
            (exactRationalLiteral (1338772896556255299) 102400000000000000000),
            (exactRationalLiteral (-19124889063946627) 3200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (140407707000739767637) 4915200000000000000000),
            (exactRationalLiteral (-781644554867712789) 51200000000000000000),
            (exactRationalLiteral (8525787849745621) 1600000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (7480352472966421517) 983040000000000000000),
            (exactRationalLiteral (-324991253415764001) 51200000000000000000),
            (exactRationalLiteral (5858917424689153) 1600000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1037983929196508239) 1638400000000000000000),
            (exactRationalLiteral (70078638896483331) 51200000000000000000),
            (exactRationalLiteral (-580111059335403) 64000000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-24076718838445040431) 9830400000000000000000),
            (exactRationalLiteral (7647060436490691) 20480000000000000000),
            (exactRationalLiteral (5916272810494237) 640000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (136204141410267713191) 4915200000000000000000),
            (exactRationalLiteral (1378630700815643049) 51200000000000000000),
            (exactRationalLiteral (17054408700973063) 1600000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-241109888409085240213) 9830400000000000000000),
            (exactRationalLiteral (-3150160549559970347) 102400000000000000000),
            (exactRationalLiteral (-69697115996508181) 3200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-130416009105409182833) 4915200000000000000000),
            (exactRationalLiteral (-77484143126938739) 10240000000000000000),
            (exactRationalLiteral (7140917340642031) 1600000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (33067250253805031909) 2457600000000000000000),
            (exactRationalLiteral (257813354155009747) 25600000000000000000),
            (exactRationalLiteral (531720536066933) 800000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (7288809816134213341) 983040000000000000000),
            (exactRationalLiteral (439123272834559807) 51200000000000000000),
            (exactRationalLiteral (3693941643758653) 320000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1168570637548346913) 1638400000000000000000),
            (exactRationalLiteral (-1184560691661353661) 51200000000000000000),
            (exactRationalLiteral (-61980394237471779) 1600000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-4139393987735962699) 614400000000000000000),
            (exactRationalLiteral (466375808815979839) 6400000000000000000),
            (exactRationalLiteral (27351349214045261) 200000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (728891039496261619357) 9830400000000000000000),
            (exactRationalLiteral (-5823169743070802237) 102400000000000000000),
            (exactRationalLiteral (-179911672091062279) 640000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-917769307226826057877) 9830400000000000000000),
            (exactRationalLiteral (-6844504692832950187) 102400000000000000000),
            (exactRationalLiteral (965213795320629227) 3200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (23042135663697242919) 1638400000000000000000),
            (exactRationalLiteral (5611874614113346507) 51200000000000000000),
            (exactRationalLiteral (-51005689214425551) 320000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2254233464573386701) 163840000000000000000),
            (exactRationalLiteral (-203737928244438879) 5120000000000000000),
            (exactRationalLiteral (4981489896689751) 160000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (3632883487353533) 9830400000000000000000),
            (exactRationalLiteral (-3632883487353533) 102400000000000000000),
            (exactRationalLiteral (3632883487353533) 3200000000000000000),
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
          (exactRationalLiteral (3632883487353533) 1228800000000000000000),
          (exactRationalLiteral (923477151958257691) 61440000000000000000),
          (exactRationalLiteral (86641834747143) 5000000000000000),
          (exactRationalLiteral (2378707769202221) 25000000000000000),
          (exactRationalLiteral (92963156434078527373) 1228800000000000000000),
          (exactRationalLiteral (682198350046113241) 76800000000000000000),
          (exactRationalLiteral (4608042128137) 3125000000000000),
          (exactRationalLiteral (2308202398570141) 300000000000000000),
          (exactRationalLiteral (4131126972620123) 300000000000000000),
          (exactRationalLiteral (2676521536101071) 100000000000000000),
          (exactRationalLiteral (637744755288719) 25000000000000000),
          (exactRationalLiteral (8568813985829011) 300000000000000000),
          (exactRationalLiteral (62871886728346833) 25600000000000000000),
          (exactRationalLiteral (40038179607619) 60000000000000000),
          (exactRationalLiteral (4799266649416283921) 614400000000000000000),
          (exactRationalLiteral (17847344261385311477) 614400000000000000000),
          (exactRationalLiteral (19609560252436158691) 1228800000000000000000),
          (exactRationalLiteral (20771191274082634637) 1228800000000000000000),
          (exactRationalLiteral (302382173351085727) 61440000000000000000),
          (exactRationalLiteral (13126592130968210791) 153600000000000000000),
          (exactRationalLiteral (110189682055832651371) 614400000000000000000),
          (exactRationalLiteral (13126592130968210791) 153600000000000000000),
          (exactRationalLiteral (302382173351085727) 61440000000000000000),
          (exactRationalLiteral (20771191274082634637) 1228800000000000000000),
          (exactRationalLiteral (19609560252436158691) 1228800000000000000000),
          (exactRationalLiteral (17847344261385311477) 614400000000000000000),
          (exactRationalLiteral (4799266649416283921) 614400000000000000000),
          (exactRationalLiteral (40038179607619) 60000000000000000),
          (exactRationalLiteral (62871886728346833) 25600000000000000000),
          (exactRationalLiteral (8568813985829011) 300000000000000000),
          (exactRationalLiteral (637744755288719) 25000000000000000),
          (exactRationalLiteral (2676521536101071) 100000000000000000),
          (exactRationalLiteral (4131126972620123) 300000000000000000),
          (exactRationalLiteral (2308202398570141) 300000000000000000),
          (exactRationalLiteral (4608042128137) 3125000000000000),
          (exactRationalLiteral (682198350046113241) 76800000000000000000),
          (exactRationalLiteral (92963156434078527373) 1228800000000000000000),
          (exactRationalLiteral (2378707769202221) 25000000000000000),
          (exactRationalLiteral (86641834747143) 5000000000000000),
          (exactRationalLiteral (923477151958257691) 61440000000000000000),
          (exactRationalLiteral (3632883487353533) 1228800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (31, 47),
      (31, 31),
      (31, 15),
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
      (27, 48)
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
        cell := 8
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (752865296771777) 480000000000000000),
            (exactRationalLiteral (-752865296771777) 80000000000000000),
            (exactRationalLiteral (752865296771777) 40000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (19248733207282643) 600000000000000000),
            (exactRationalLiteral (-2244317294158487) 100000000000000000),
            (exactRationalLiteral (-684764268709913) 10000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-142077787717305917) 2400000000000000000),
            (exactRationalLiteral (3842469638543) 25600000000000),
            (exactRationalLiteral (14842567463325499) 200000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8256990251353489) 600000000000000000),
            (exactRationalLiteral (-43611948717965917) 200000000000000000),
            (exactRationalLiteral (82680775880863) 10000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (26011802955833563) 480000000000000000),
            (exactRationalLiteral (46692758947123811) 400000000000000000),
            (exactRationalLiteral (-14415395411011561) 200000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-40153440606696413) 2400000000000000000),
            (exactRationalLiteral (-8071335104895209) 400000000000000000),
            (exactRationalLiteral (10229529326677603) 200000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7635001843852001) 600000000000000000),
            (exactRationalLiteral (44406193705353) 8000000000000000),
            (exactRationalLiteral (-977147743893889) 50000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (11876417452022903) 600000000000000000),
            (exactRationalLiteral (3130034889381719) 200000000000000000),
            (exactRationalLiteral (526744339837067) 50000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2490707412306647) 100000000000000000),
            (exactRationalLiteral (4666128247758159) 200000000000000000),
            (exactRationalLiteral (282335888955819) 5000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-137477004918729287) 2400000000000000000),
            (exactRationalLiteral (-46058552799970523) 400000000000000000),
            (exactRationalLiteral (-28721156061613319) 200000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (42649820235137957) 800000000000000000),
            (exactRationalLiteral (7031542161037713) 80000000000000000),
            (exactRationalLiteral (21955465941771471) 200000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2541482066624383) 1200000000000000000),
            (exactRationalLiteral (-248302542241447) 50000000000000000),
            (exactRationalLiteral (-2165332965915427) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (-2269729304325409) 2400000000000000000),
            (exactRationalLiteral (-2594468390326943) 400000000000000000),
            (exactRationalLiteral (-40106779006873) 8000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (1028363248912287) 200000000000000000),
            (exactRationalLiteral (-82347769863591) 25000000000000000),
            (exactRationalLiteral (93413891985153) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (17394075357602399) 800000000000000000),
            (exactRationalLiteral (-4287039104354331) 400000000000000000),
            (exactRationalLiteral (691815823834917) 200000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2007305671066057) 200000000000000000),
            (exactRationalLiteral (24868310272369) 3125000000000000),
            (exactRationalLiteral (-199578274361853) 50000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (-33033570660653389) 2400000000000000000),
            (exactRationalLiteral (1960529494376103) 400000000000000000),
            (exactRationalLiteral (-181845115063237) 200000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3147963736127123) 800000000000000000),
            (exactRationalLiteral (731328588736319) 400000000000000000),
            (exactRationalLiteral (-1390807156809) 8000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-159916340046811181) 2400000000000000000),
            (exactRationalLiteral (11396823840797237) 400000000000000000),
            (exactRationalLiteral (-1541327748053069) 200000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (165011338508892499) 1200000000000000000),
            (exactRationalLiteral (-12692646301146343) 200000000000000000),
            (exactRationalLiteral (1718630326278043) 100000000000000000),
            (exactRationalLiteral (-196301193326517) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-159916340046811181) 2400000000000000000),
            (exactRationalLiteral (11396823840797237) 400000000000000000),
            (exactRationalLiteral (-1541327748053069) 200000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-3147963736127123) 800000000000000000),
            (exactRationalLiteral (731328588736319) 400000000000000000),
            (exactRationalLiteral (-1390807156809) 8000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-33033570660653389) 2400000000000000000),
            (exactRationalLiteral (1960529494376103) 400000000000000000),
            (exactRationalLiteral (-181845115063237) 200000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2007305671066057) 200000000000000000),
            (exactRationalLiteral (24868310272369) 3125000000000000),
            (exactRationalLiteral (-199578274361853) 50000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (17394075357602399) 800000000000000000),
            (exactRationalLiteral (-4287039104354331) 400000000000000000),
            (exactRationalLiteral (691815823834917) 200000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1028363248912287) 200000000000000000),
            (exactRationalLiteral (-82347769863591) 25000000000000000),
            (exactRationalLiteral (93413891985153) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-2269729304325409) 2400000000000000000),
            (exactRationalLiteral (-2594468390326943) 400000000000000000),
            (exactRationalLiteral (-40106779006873) 8000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-2541482066624383) 1200000000000000000),
            (exactRationalLiteral (-248302542241447) 50000000000000000),
            (exactRationalLiteral (-2165332965915427) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (42649820235137957) 800000000000000000),
            (exactRationalLiteral (7031542161037713) 80000000000000000),
            (exactRationalLiteral (21955465941771471) 200000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-137477004918729287) 2400000000000000000),
            (exactRationalLiteral (-46058552799970523) 400000000000000000),
            (exactRationalLiteral (-28721156061613319) 200000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2490707412306647) 100000000000000000),
            (exactRationalLiteral (4666128247758159) 200000000000000000),
            (exactRationalLiteral (282335888955819) 5000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (11876417452022903) 600000000000000000),
            (exactRationalLiteral (3130034889381719) 200000000000000000),
            (exactRationalLiteral (526744339837067) 50000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (7635001843852001) 600000000000000000),
            (exactRationalLiteral (44406193705353) 8000000000000000),
            (exactRationalLiteral (-977147743893889) 50000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-40153440606696413) 2400000000000000000),
            (exactRationalLiteral (-8071335104895209) 400000000000000000),
            (exactRationalLiteral (10229529326677603) 200000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (26011802955833563) 480000000000000000),
            (exactRationalLiteral (46692758947123811) 400000000000000000),
            (exactRationalLiteral (-14415395411011561) 200000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8256990251353489) 600000000000000000),
            (exactRationalLiteral (-43611948717965917) 200000000000000000),
            (exactRationalLiteral (82680775880863) 10000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-142077787717305917) 2400000000000000000),
            (exactRationalLiteral (3842469638543) 25600000000000),
            (exactRationalLiteral (14842567463325499) 200000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (19248733207282643) 600000000000000000),
            (exactRationalLiteral (-2244317294158487) 100000000000000000),
            (exactRationalLiteral (-684764268709913) 10000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (752865296771777) 480000000000000000),
            (exactRationalLiteral (-752865296771777) 80000000000000000),
            (exactRationalLiteral (752865296771777) 40000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (0 : ℚ),
          (exactRationalLiteral (752865296771777) 60000000000000000),
          (exactRationalLiteral (472344886475671) 9375000000000000),
          (exactRationalLiteral (832090147104641) 7500000000000000),
          (exactRationalLiteral (28643959928971939) 300000000000000000),
          (exactRationalLiteral (4876111408114573) 50000000000000000),
          (exactRationalLiteral (1598800710014593) 50000000000000000),
          (exactRationalLiteral (109306899597) 6103515625000),
          (exactRationalLiteral (3108507832971327) 100000000000000000),
          (exactRationalLiteral (1501692356610239) 50000000000000000),
          (exactRationalLiteral (48257181212427683) 300000000000000000),
          (exactRationalLiteral (1994257532342653) 15000000000000000),
          (exactRationalLiteral (1263412987075841) 100000000000000000),
          (exactRationalLiteral (126635444208193) 25000000000000000),
          (exactRationalLiteral (222439850090833) 30000000000000000),
          (exactRationalLiteral (263381604456893) 9375000000000000),
          (exactRationalLiteral (189261036501229) 12500000000000000),
          (exactRationalLiteral (165088796038881) 10000000000000000),
          (exactRationalLiteral (241231833581281) 50000000000000000),
          (exactRationalLiteral (8305874674326991) 100000000000000000),
          (exactRationalLiteral (26104258996393151) 150000000000000000),
          (exactRationalLiteral (8305874674326991) 100000000000000000),
          (exactRationalLiteral (241231833581281) 50000000000000000),
          (exactRationalLiteral (165088796038881) 10000000000000000),
          (exactRationalLiteral (189261036501229) 12500000000000000),
          (exactRationalLiteral (263381604456893) 9375000000000000),
          (exactRationalLiteral (222439850090833) 30000000000000000),
          (exactRationalLiteral (126635444208193) 25000000000000000),
          (exactRationalLiteral (1263412987075841) 100000000000000000),
          (exactRationalLiteral (1994257532342653) 15000000000000000),
          (exactRationalLiteral (48257181212427683) 300000000000000000),
          (exactRationalLiteral (1501692356610239) 50000000000000000),
          (exactRationalLiteral (3108507832971327) 100000000000000000),
          (exactRationalLiteral (109306899597) 6103515625000),
          (exactRationalLiteral (1598800710014593) 50000000000000000),
          (exactRationalLiteral (4876111408114573) 50000000000000000),
          (exactRationalLiteral (28643959928971939) 300000000000000000),
          (exactRationalLiteral (832090147104641) 7500000000000000),
          (exactRationalLiteral (472344886475671) 9375000000000000),
          (exactRationalLiteral (752865296771777) 60000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (46, 30),
      (46, 29),
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
      (46, 13)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 8
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (6775787670945993) 1280000000000000000),
            (exactRationalLiteral (-6775787670945993) 320000000000000000),
            (exactRationalLiteral (2258595890315331) 80000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (155065544237413349) 4800000000000000000),
            (exactRationalLiteral (10031217087016561) 400000000000000000),
            (exactRationalLiteral (-12160843576551379) 100000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1718720050394687513) 19200000000000000000),
            (exactRationalLiteral (5258967150600647) 64000000000000000),
            (exactRationalLiteral (78995038717270327) 400000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (365898823482495877) 9600000000000000000),
            (exactRationalLiteral (-29492292448561421) 160000000000000000),
            (exactRationalLiteral (-28639948146673823) 200000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (436552816853983739) 19200000000000000000),
            (exactRationalLiteral (201546438980345171) 1600000000000000000),
            (exactRationalLiteral (2811077526034639) 80000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-181282456677194417) 19200000000000000000),
            (exactRationalLiteral (-54915328683860009) 1600000000000000000),
            (exactRationalLiteral (2170929610923967) 400000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (100268555361140819) 9600000000000000000),
            (exactRationalLiteral (9101644423845041) 800000000000000000),
            (exactRationalLiteral (-150486815546837) 40000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (10518966950225871) 640000000000000000),
            (exactRationalLiteral (9304873223272899) 800000000000000000),
            (exactRationalLiteral (1108288974905709) 200000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-88797560653148497) 3200000000000000000),
            (exactRationalLiteral (1249179954174867) 800000000000000000),
            (exactRationalLiteral (6121897478625009) 200000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-695199023923927283) 19200000000000000000),
            (exactRationalLiteral (-93590905149369467) 1600000000000000000),
            (exactRationalLiteral (-33200993927285987) 400000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (713643737403146513) 19200000000000000000),
            (exactRationalLiteral (72601193682198877) 1600000000000000000),
            (exactRationalLiteral (24118717655012441) 400000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3043581321209351) 1600000000000000000),
            (exactRationalLiteral (386161703539123) 200000000000000000),
            (exactRationalLiteral (-118682155818879) 20000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (2018543047151303) 6400000000000000000),
            (exactRationalLiteral (-5463055403785287) 1600000000000000000),
            (exactRationalLiteral (-581895841435767) 80000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (14644593310009711) 2400000000000000000),
            (exactRationalLiteral (-446628056629829) 100000000000000000),
            (exactRationalLiteral (141060062365777) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (473360072661308717) 19200000000000000000),
            (exactRationalLiteral (-20222319596346659) 1600000000000000000),
            (exactRationalLiteral (1690531531259501) 400000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-983312617099567) 80000000000000000),
            (exactRationalLiteral (2028988470969241) 200000000000000000),
            (exactRationalLiteral (-59459584793943) 12500000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (-289046606468479801) 19200000000000000000),
            (exactRationalLiteral (8730114998117391) 1600000000000000000),
            (exactRationalLiteral (-104861358097301) 80000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-28124211435319539) 6400000000000000000),
            (exactRationalLiteral (2901335571176663) 1600000000000000000),
            (exactRationalLiteral (93519141609063) 400000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1425950770322860391) 19200000000000000000),
            (exactRationalLiteral (52362803725886909) 1600000000000000000),
            (exactRationalLiteral (-3692852866591823) 400000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (1483303149222543917) 9600000000000000000),
            (exactRationalLiteral (-11646802017935419) 160000000000000000),
            (exactRationalLiteral (4026164232535637) 200000000000000000),
            (exactRationalLiteral (-196301193326517) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1425950770322860391) 19200000000000000000),
            (exactRationalLiteral (52362803725886909) 1600000000000000000),
            (exactRationalLiteral (-3692852866591823) 400000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-28124211435319539) 6400000000000000000),
            (exactRationalLiteral (2901335571176663) 1600000000000000000),
            (exactRationalLiteral (93519141609063) 400000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-289046606468479801) 19200000000000000000),
            (exactRationalLiteral (8730114998117391) 1600000000000000000),
            (exactRationalLiteral (-104861358097301) 80000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-983312617099567) 80000000000000000),
            (exactRationalLiteral (2028988470969241) 200000000000000000),
            (exactRationalLiteral (-59459584793943) 12500000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (473360072661308717) 19200000000000000000),
            (exactRationalLiteral (-20222319596346659) 1600000000000000000),
            (exactRationalLiteral (1690531531259501) 400000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (14644593310009711) 2400000000000000000),
            (exactRationalLiteral (-446628056629829) 100000000000000000),
            (exactRationalLiteral (141060062365777) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (2018543047151303) 6400000000000000000),
            (exactRationalLiteral (-5463055403785287) 1600000000000000000),
            (exactRationalLiteral (-581895841435767) 80000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-3043581321209351) 1600000000000000000),
            (exactRationalLiteral (386161703539123) 200000000000000000),
            (exactRationalLiteral (-118682155818879) 20000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (713643737403146513) 19200000000000000000),
            (exactRationalLiteral (72601193682198877) 1600000000000000000),
            (exactRationalLiteral (24118717655012441) 400000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-695199023923927283) 19200000000000000000),
            (exactRationalLiteral (-93590905149369467) 1600000000000000000),
            (exactRationalLiteral (-33200993927285987) 400000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-88797560653148497) 3200000000000000000),
            (exactRationalLiteral (1249179954174867) 800000000000000000),
            (exactRationalLiteral (6121897478625009) 200000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (10518966950225871) 640000000000000000),
            (exactRationalLiteral (9304873223272899) 800000000000000000),
            (exactRationalLiteral (1108288974905709) 200000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (100268555361140819) 9600000000000000000),
            (exactRationalLiteral (9101644423845041) 800000000000000000),
            (exactRationalLiteral (-150486815546837) 40000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-181282456677194417) 19200000000000000000),
            (exactRationalLiteral (-54915328683860009) 1600000000000000000),
            (exactRationalLiteral (2170929610923967) 400000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (436552816853983739) 19200000000000000000),
            (exactRationalLiteral (201546438980345171) 1600000000000000000),
            (exactRationalLiteral (2811077526034639) 80000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (365898823482495877) 9600000000000000000),
            (exactRationalLiteral (-29492292448561421) 160000000000000000),
            (exactRationalLiteral (-28639948146673823) 200000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1718720050394687513) 19200000000000000000),
            (exactRationalLiteral (5258967150600647) 64000000000000000),
            (exactRationalLiteral (78995038717270327) 400000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (155065544237413349) 4800000000000000000),
            (exactRationalLiteral (10031217087016561) 400000000000000000),
            (exactRationalLiteral (-12160843576551379) 100000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (6775787670945993) 1280000000000000000),
            (exactRationalLiteral (-6775787670945993) 320000000000000000),
            (exactRationalLiteral (2258595890315331) 80000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (0 : ℚ),
          (exactRationalLiteral (752865296771777) 60000000000000000),
          (exactRationalLiteral (2149305050144113) 60000000000000000),
          (exactRationalLiteral (15457024778653073) 150000000000000000),
          (exactRationalLiteral (1441812087722093) 20000000000000000),
          (exactRationalLiteral (26011802955833563) 480000000000000000),
          (exactRationalLiteral (40153440606696413) 2400000000000000000),
          (exactRationalLiteral (7635001843852001) 600000000000000000),
          (exactRationalLiteral (11876417452022903) 600000000000000000),
          (exactRationalLiteral (11518205731812641) 400000000000000000),
          (exactRationalLiteral (137477004918729287) 2400000000000000000),
          (exactRationalLiteral (42649820235137957) 800000000000000000),
          (exactRationalLiteral (728501520957809) 300000000000000000),
          (exactRationalLiteral (2269729304325409) 2400000000000000000),
          (exactRationalLiteral (222439850090833) 30000000000000000),
          (exactRationalLiteral (263381604456893) 9375000000000000),
          (exactRationalLiteral (189261036501229) 12500000000000000),
          (exactRationalLiteral (165088796038881) 10000000000000000),
          (exactRationalLiteral (241231833581281) 50000000000000000),
          (exactRationalLiteral (8305874674326991) 100000000000000000),
          (exactRationalLiteral (26104258996393151) 150000000000000000),
          (exactRationalLiteral (8305874674326991) 100000000000000000),
          (exactRationalLiteral (241231833581281) 50000000000000000),
          (exactRationalLiteral (165088796038881) 10000000000000000),
          (exactRationalLiteral (189261036501229) 12500000000000000),
          (exactRationalLiteral (263381604456893) 9375000000000000),
          (exactRationalLiteral (222439850090833) 30000000000000000),
          (exactRationalLiteral (2269729304325409) 2400000000000000000),
          (exactRationalLiteral (728501520957809) 300000000000000000),
          (exactRationalLiteral (42649820235137957) 800000000000000000),
          (exactRationalLiteral (137477004918729287) 2400000000000000000),
          (exactRationalLiteral (11518205731812641) 400000000000000000),
          (exactRationalLiteral (11876417452022903) 600000000000000000),
          (exactRationalLiteral (7635001843852001) 600000000000000000),
          (exactRationalLiteral (40153440606696413) 2400000000000000000),
          (exactRationalLiteral (26011802955833563) 480000000000000000),
          (exactRationalLiteral (1441812087722093) 20000000000000000),
          (exactRationalLiteral (15457024778653073) 150000000000000000),
          (exactRationalLiteral (2149305050144113) 60000000000000000),
          (exactRationalLiteral (752865296771777) 60000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (45, 20),
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
      (44, 51)
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
      true
    ]
  }
]

/-- All centered cubic, true Bernstein, center and radius checks are exact. -/
theorem generatorCoordinates32_valid : ∀ i, (generatorCoordinates32 i).IsValid := by
  have h : ∀ i, (generatorCoordinates32 i).FastIsValid := by
    unfold GeneratorCoordinateData.FastIsValid GeneratorCubicIntervalData.FastIsValid
    decide +kernel
  intro i
  exact GeneratorCoordinateData.isValid_of_fast (h i)

/-- Actual coordinate interval candidates, block 33. -/
def generatorCoordinates33 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 8
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (752865296771777) 3840000000000000000),
            (exactRationalLiteral (-752865296771777) 320000000000000000),
            (exactRationalLiteral (752865296771777) 80000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (37276110318838053) 1600000000000000000),
            (exactRationalLiteral (-17359353661379959) 400000000000000000),
            (exactRationalLiteral (-1534441797646881) 100000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-125471247840767057) 6400000000000000000),
            (exactRationalLiteral (250214718471620167) 1600000000000000000),
            (exactRationalLiteral (-19624768863968331) 400000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-41346721228006931) 640000000000000000),
            (exactRationalLiteral (-28169400034467613) 160000000000000000),
            (exactRationalLiteral (31947179181908343) 200000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (490468891560187523) 6400000000000000000),
            (exactRationalLiteral (86223275692252683) 1600000000000000000),
            (exactRationalLiteral (-71716969274219439) 400000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-22561216073987797) 1280000000000000000),
            (exactRationalLiteral (5384181185912163) 320000000000000000),
            (exactRationalLiteral (7749437539157289) 80000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (120599957788669877) 9600000000000000000),
            (exactRationalLiteral (-6532719478457183) 800000000000000000),
            (exactRationalLiteral (-7064747873416927) 200000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (234902718367434439) 9600000000000000000),
            (exactRationalLiteral (17732782660665971) 800000000000000000),
            (exactRationalLiteral (3105665743790827) 200000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-48020842618011391) 3200000000000000000),
            (exactRationalLiteral (46422922187105907) 800000000000000000),
            (exactRationalLiteral (16464973637840511) 200000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-616362309171700379) 6400000000000000000),
            (exactRationalLiteral (-323360153642276019) 1600000000000000000),
            (exactRationalLiteral (-81683630319167289) 400000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (63880529007389323) 768000000000000000),
            (exactRationalLiteral (49648984243274129) 320000000000000000),
            (exactRationalLiteral (63703146112073443) 400000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-24193110364859573) 4800000000000000000),
            (exactRationalLiteral (-3944504228291731) 200000000000000000),
            (exactRationalLiteral (-3737255152736459) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (-54403331712722353) 19200000000000000000),
            (exactRationalLiteral (-13484411205159887) 1600000000000000000),
            (exactRationalLiteral (-220239738701693) 80000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (2119321603159219) 480000000000000000),
            (exactRationalLiteral (-259800272659523) 100000000000000000),
            (exactRationalLiteral (45767721604529) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (369857334389625439) 19200000000000000000),
            (exactRationalLiteral (-14687793005667323) 1600000000000000000),
            (exactRationalLiteral (1076731764080167) 400000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1656118936564123) 200000000000000000),
            (exactRationalLiteral (1230675373521829) 200000000000000000),
            (exactRationalLiteral (-80659104773967) 25000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (-80557555160911089) 6400000000000000000),
            (exactRationalLiteral (1455070815522299) 320000000000000000),
            (exactRationalLiteral (-203073669766443) 400000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-22382289058395329) 6400000000000000000),
            (exactRationalLiteral (2623174139814863) 1600000000000000000),
            (exactRationalLiteral (-232599857289963) 400000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-383735534467585111) 6400000000000000000),
            (exactRationalLiteral (40032181741462357) 1600000000000000000),
            (exactRationalLiteral (-2472458125620453) 400000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (1177501830835072583) 9600000000000000000),
            (exactRationalLiteral (-44484967479452751) 800000000000000000),
            (exactRationalLiteral (569671414515307) 40000000000000000),
            (exactRationalLiteral (-196301193326517) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-383735534467585111) 6400000000000000000),
            (exactRationalLiteral (40032181741462357) 1600000000000000000),
            (exactRationalLiteral (-2472458125620453) 400000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-22382289058395329) 6400000000000000000),
            (exactRationalLiteral (2623174139814863) 1600000000000000000),
            (exactRationalLiteral (-232599857289963) 400000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-80557555160911089) 6400000000000000000),
            (exactRationalLiteral (1455070815522299) 320000000000000000),
            (exactRationalLiteral (-203073669766443) 400000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1656118936564123) 200000000000000000),
            (exactRationalLiteral (1230675373521829) 200000000000000000),
            (exactRationalLiteral (-80659104773967) 25000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (369857334389625439) 19200000000000000000),
            (exactRationalLiteral (-14687793005667323) 1600000000000000000),
            (exactRationalLiteral (1076731764080167) 400000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2119321603159219) 480000000000000000),
            (exactRationalLiteral (-259800272659523) 100000000000000000),
            (exactRationalLiteral (45767721604529) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-54403331712722353) 19200000000000000000),
            (exactRationalLiteral (-13484411205159887) 1600000000000000000),
            (exactRationalLiteral (-220239738701693) 80000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-24193110364859573) 4800000000000000000),
            (exactRationalLiteral (-3944504228291731) 200000000000000000),
            (exactRationalLiteral (-3737255152736459) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (63880529007389323) 768000000000000000),
            (exactRationalLiteral (49648984243274129) 320000000000000000),
            (exactRationalLiteral (63703146112073443) 400000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-616362309171700379) 6400000000000000000),
            (exactRationalLiteral (-323360153642276019) 1600000000000000000),
            (exactRationalLiteral (-81683630319167289) 400000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-48020842618011391) 3200000000000000000),
            (exactRationalLiteral (46422922187105907) 800000000000000000),
            (exactRationalLiteral (16464973637840511) 200000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (234902718367434439) 9600000000000000000),
            (exactRationalLiteral (17732782660665971) 800000000000000000),
            (exactRationalLiteral (3105665743790827) 200000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (120599957788669877) 9600000000000000000),
            (exactRationalLiteral (-6532719478457183) 800000000000000000),
            (exactRationalLiteral (-7064747873416927) 200000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-22561216073987797) 1280000000000000000),
            (exactRationalLiteral (5384181185912163) 320000000000000000),
            (exactRationalLiteral (7749437539157289) 80000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (490468891560187523) 6400000000000000000),
            (exactRationalLiteral (86223275692252683) 1600000000000000000),
            (exactRationalLiteral (-71716969274219439) 400000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-41346721228006931) 640000000000000000),
            (exactRationalLiteral (-28169400034467613) 160000000000000000),
            (exactRationalLiteral (31947179181908343) 200000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-125471247840767057) 6400000000000000000),
            (exactRationalLiteral (250214718471620167) 1600000000000000000),
            (exactRationalLiteral (-19624768863968331) 400000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (37276110318838053) 1600000000000000000),
            (exactRationalLiteral (-17359353661379959) 400000000000000000),
            (exactRationalLiteral (-1534441797646881) 100000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (752865296771777) 3840000000000000000),
            (exactRationalLiteral (-752865296771777) 320000000000000000),
            (exactRationalLiteral (752865296771777) 80000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (0 : ℚ),
          (exactRationalLiteral (752865296771777) 480000000000000000),
          (exactRationalLiteral (19248733207282643) 600000000000000000),
          (exactRationalLiteral (142077787717305917) 2400000000000000000),
          (exactRationalLiteral (28643959928971939) 300000000000000000),
          (exactRationalLiteral (52257284315600969) 600000000000000000),
          (exactRationalLiteral (24112387855795811) 1200000000000000000),
          (exactRationalLiteral (16380158530337827) 1200000000000000000),
          (exactRationalLiteral (3108507832971327) 100000000000000000),
          (exactRationalLiteral (2490707412306647) 100000000000000000),
          (exactRationalLiteral (48257181212427683) 300000000000000000),
          (exactRationalLiteral (1994257532342653) 15000000000000000),
          (exactRationalLiteral (1263412987075841) 100000000000000000),
          (exactRationalLiteral (126635444208193) 25000000000000000),
          (exactRationalLiteral (1028363248912287) 200000000000000000),
          (exactRationalLiteral (17394075357602399) 800000000000000000),
          (exactRationalLiteral (2007305671066057) 200000000000000000),
          (exactRationalLiteral (33033570660653389) 2400000000000000000),
          (exactRationalLiteral (3147963736127123) 800000000000000000),
          (exactRationalLiteral (159916340046811181) 2400000000000000000),
          (exactRationalLiteral (165011338508892499) 1200000000000000000),
          (exactRationalLiteral (159916340046811181) 2400000000000000000),
          (exactRationalLiteral (3147963736127123) 800000000000000000),
          (exactRationalLiteral (33033570660653389) 2400000000000000000),
          (exactRationalLiteral (2007305671066057) 200000000000000000),
          (exactRationalLiteral (17394075357602399) 800000000000000000),
          (exactRationalLiteral (1028363248912287) 200000000000000000),
          (exactRationalLiteral (126635444208193) 25000000000000000),
          (exactRationalLiteral (1263412987075841) 100000000000000000),
          (exactRationalLiteral (1994257532342653) 15000000000000000),
          (exactRationalLiteral (48257181212427683) 300000000000000000),
          (exactRationalLiteral (2490707412306647) 100000000000000000),
          (exactRationalLiteral (3108507832971327) 100000000000000000),
          (exactRationalLiteral (16380158530337827) 1200000000000000000),
          (exactRationalLiteral (24112387855795811) 1200000000000000000),
          (exactRationalLiteral (52257284315600969) 600000000000000000),
          (exactRationalLiteral (28643959928971939) 300000000000000000),
          (exactRationalLiteral (142077787717305917) 2400000000000000000),
          (exactRationalLiteral (19248733207282643) 600000000000000000),
          (exactRationalLiteral (752865296771777) 480000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (45, 21),
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
      (44, 50)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 8
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (258232796792719511) 30720000000000000000),
            (exactRationalLiteral (-36890399541817073) 1280000000000000000),
            (exactRationalLiteral (5270057077402439) 160000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (1041871486506347537) 38400000000000000000),
            (exactRationalLiteral (94081443543724009) 1600000000000000000),
            (exactRationalLiteral (-29634888042555007) 200000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-14804170412243452913) 153600000000000000000),
            (exactRationalLiteral (160606656400364063) 6400000000000000000),
            (exactRationalLiteral (207299981225159983) 800000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (898918976445863651) 15360000000000000000),
            (exactRationalLiteral (-88998498544048409) 640000000000000000),
            (exactRationalLiteral (-87573459957638729) 400000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1201083771300963347) 153600000000000000000),
            (exactRationalLiteral (707078026948491587) 6400000000000000000),
            (exactRationalLiteral (70996953712542707) 800000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-159307652117624533) 30720000000000000000),
            (exactRationalLiteral (-42011380827340933) 1280000000000000000),
            (exactRationalLiteral (-2789253964116661) 160000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (691570262234422321) 76800000000000000000),
            (exactRationalLiteral (36260157108475533) 3200000000000000000),
            (exactRationalLiteral (1651288742373001) 400000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1156268600812821427) 76800000000000000000),
            (exactRationalLiteral (33785025377911319) 3200000000000000000),
            (exactRationalLiteral (1217889565368859) 400000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-704857256111173343) 25600000000000000000),
            (exactRationalLiteral (-14319332018192817) 3200000000000000000),
            (exactRationalLiteral (7072256877642267) 400000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-4613465974966759931) 153600000000000000000),
            (exactRationalLiteral (-265800963084274571) 6400000000000000000),
            (exactRationalLiteral (-42160669658631323) 800000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (66171408889871063) 2048000000000000000),
            (exactRationalLiteral (42744423667455249) 1280000000000000000),
            (exactRationalLiteral (28445221081494381) 800000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-42151187540854357) 19200000000000000000),
            (exactRationalLiteral (972753639467383) 400000000000000000),
            (exactRationalLiteral (192550314316121) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (95640682477146521) 153600000000000000000),
            (exactRationalLiteral (-9310164529590623) 6400000000000000000),
            (exactRationalLiteral (-1344619734238571) 160000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (4292327546125629) 640000000000000000),
            (exactRationalLiteral (-1046227718220591) 200000000000000000),
            (exactRationalLiteral (164883147556089) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (1346666168505925439) 51200000000000000000),
            (exactRationalLiteral (-87958304394014307) 6400000000000000000),
            (exactRationalLiteral (3687962946108669) 800000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-87269393285131841) 6400000000000000000),
            (exactRationalLiteral (9105567305393971) 800000000000000000),
            (exactRationalLiteral (-513936743165463) 100000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (-2420440689028526161) 153600000000000000000),
            (exactRationalLiteral (7435660742955123) 1280000000000000000),
            (exactRationalLiteral (-1209230141333041) 800000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-236357642317561667) 51200000000000000000),
            (exactRationalLiteral (11068206218820887) 6400000000000000000),
            (exactRationalLiteral (350097782667639) 800000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-12058727121863562659) 153600000000000000000),
            (exactRationalLiteral (224832823740400613) 6400000000000000000),
            (exactRationalLiteral (-7995903103669331) 800000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (12589979203831669849) 76800000000000000000),
            (exactRationalLiteral (-249629600868830479) 3200000000000000000),
            (exactRationalLiteral (345649281802033) 16000000000000000),
            (exactRationalLiteral (-196301193326517) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-12058727121863562659) 153600000000000000000),
            (exactRationalLiteral (224832823740400613) 6400000000000000000),
            (exactRationalLiteral (-7995903103669331) 800000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-236357642317561667) 51200000000000000000),
            (exactRationalLiteral (11068206218820887) 6400000000000000000),
            (exactRationalLiteral (350097782667639) 800000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-2420440689028526161) 153600000000000000000),
            (exactRationalLiteral (7435660742955123) 1280000000000000000),
            (exactRationalLiteral (-1209230141333041) 800000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-87269393285131841) 6400000000000000000),
            (exactRationalLiteral (9105567305393971) 800000000000000000),
            (exactRationalLiteral (-513936743165463) 100000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (1346666168505925439) 51200000000000000000),
            (exactRationalLiteral (-87958304394014307) 6400000000000000000),
            (exactRationalLiteral (3687962946108669) 800000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4292327546125629) 640000000000000000),
            (exactRationalLiteral (-1046227718220591) 200000000000000000),
            (exactRationalLiteral (164883147556089) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (95640682477146521) 153600000000000000000),
            (exactRationalLiteral (-9310164529590623) 6400000000000000000),
            (exactRationalLiteral (-1344619734238571) 160000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-42151187540854357) 19200000000000000000),
            (exactRationalLiteral (972753639467383) 400000000000000000),
            (exactRationalLiteral (192550314316121) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (66171408889871063) 2048000000000000000),
            (exactRationalLiteral (42744423667455249) 1280000000000000000),
            (exactRationalLiteral (28445221081494381) 800000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4613465974966759931) 153600000000000000000),
            (exactRationalLiteral (-265800963084274571) 6400000000000000000),
            (exactRationalLiteral (-42160669658631323) 800000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-704857256111173343) 25600000000000000000),
            (exactRationalLiteral (-14319332018192817) 3200000000000000000),
            (exactRationalLiteral (7072256877642267) 400000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1156268600812821427) 76800000000000000000),
            (exactRationalLiteral (33785025377911319) 3200000000000000000),
            (exactRationalLiteral (1217889565368859) 400000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (691570262234422321) 76800000000000000000),
            (exactRationalLiteral (36260157108475533) 3200000000000000000),
            (exactRationalLiteral (1651288742373001) 400000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-159307652117624533) 30720000000000000000),
            (exactRationalLiteral (-42011380827340933) 1280000000000000000),
            (exactRationalLiteral (-2789253964116661) 160000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1201083771300963347) 153600000000000000000),
            (exactRationalLiteral (707078026948491587) 6400000000000000000),
            (exactRationalLiteral (70996953712542707) 800000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (898918976445863651) 15360000000000000000),
            (exactRationalLiteral (-88998498544048409) 640000000000000000),
            (exactRationalLiteral (-87573459957638729) 400000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-14804170412243452913) 153600000000000000000),
            (exactRationalLiteral (160606656400364063) 6400000000000000000),
            (exactRationalLiteral (207299981225159983) 800000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1041871486506347537) 38400000000000000000),
            (exactRationalLiteral (94081443543724009) 1600000000000000000),
            (exactRationalLiteral (-29634888042555007) 200000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (258232796792719511) 30720000000000000000),
            (exactRationalLiteral (-36890399541817073) 1280000000000000000),
            (exactRationalLiteral (5270057077402439) 160000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (0 : ℚ),
          (exactRationalLiteral (752865296771777) 60000000000000000),
          (exactRationalLiteral (155065544237413349) 4800000000000000000),
          (exactRationalLiteral (29729271393866399) 300000000000000000),
          (exactRationalLiteral (1441812087722093) 20000000000000000),
          (exactRationalLiteral (436552816853983739) 19200000000000000000),
          (exactRationalLiteral (181282456677194417) 19200000000000000000),
          (exactRationalLiteral (100268555361140819) 9600000000000000000),
          (exactRationalLiteral (10518966950225871) 640000000000000000),
          (exactRationalLiteral (44606976985603393) 1600000000000000000),
          (exactRationalLiteral (695199023923927283) 19200000000000000000),
          (exactRationalLiteral (713643737403146513) 19200000000000000000),
          (exactRationalLiteral (728501520957809) 300000000000000000),
          (exactRationalLiteral (293172098788451) 400000000000000000),
          (exactRationalLiteral (222439850090833) 30000000000000000),
          (exactRationalLiteral (263381604456893) 9375000000000000),
          (exactRationalLiteral (189261036501229) 12500000000000000),
          (exactRationalLiteral (165088796038881) 10000000000000000),
          (exactRationalLiteral (241231833581281) 50000000000000000),
          (exactRationalLiteral (8305874674326991) 100000000000000000),
          (exactRationalLiteral (26104258996393151) 150000000000000000),
          (exactRationalLiteral (8305874674326991) 100000000000000000),
          (exactRationalLiteral (241231833581281) 50000000000000000),
          (exactRationalLiteral (165088796038881) 10000000000000000),
          (exactRationalLiteral (189261036501229) 12500000000000000),
          (exactRationalLiteral (263381604456893) 9375000000000000),
          (exactRationalLiteral (222439850090833) 30000000000000000),
          (exactRationalLiteral (293172098788451) 400000000000000000),
          (exactRationalLiteral (728501520957809) 300000000000000000),
          (exactRationalLiteral (713643737403146513) 19200000000000000000),
          (exactRationalLiteral (695199023923927283) 19200000000000000000),
          (exactRationalLiteral (44606976985603393) 1600000000000000000),
          (exactRationalLiteral (10518966950225871) 640000000000000000),
          (exactRationalLiteral (100268555361140819) 9600000000000000000),
          (exactRationalLiteral (181282456677194417) 19200000000000000000),
          (exactRationalLiteral (436552816853983739) 19200000000000000000),
          (exactRationalLiteral (1441812087722093) 20000000000000000),
          (exactRationalLiteral (29729271393866399) 300000000000000000),
          (exactRationalLiteral (155065544237413349) 4800000000000000000),
          (exactRationalLiteral (752865296771777) 60000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (43, 14),
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
      (42, 13)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 8
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (752865296771777) 245760000000000000),
            (exactRationalLiteral (-752865296771777) 51200000000000000),
            (exactRationalLiteral (752865296771777) 32000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (431082366124549833) 12800000000000000000),
            (exactRationalLiteral (-3205305068687023) 1600000000000000000),
            (exactRationalLiteral (-19008486263650509) 200000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-3915803309821434457) 51200000000000000000),
            (exactRationalLiteral (792566966138526679) 6400000000000000000),
            (exactRationalLiteral (4347206945756853) 32000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (338702305243509967) 25600000000000000000),
            (exactRationalLiteral (-674112077893632629) 3200000000000000000),
            (exactRationalLiteral (-26986332629056563) 400000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1984141983308284939) 51200000000000000000),
            (exactRationalLiteral (819521127989877147) 6400000000000000000),
            (exactRationalLiteral (-14775403191849927) 800000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-692643296971966801) 51200000000000000000),
            (exactRationalLiteral (-192689467249312929) 6400000000000000000),
            (exactRationalLiteral (22629988264279173) 800000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (903697414611020563) 76800000000000000000),
            (exactRationalLiteral (30240684486602053) 3200000000000000000),
            (exactRationalLiteral (-4661025053309741) 400000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1381582934940256121) 76800000000000000000),
            (exactRationalLiteral (42651337177156991) 3200000000000000000),
            (exactRationalLiteral (3215266334253977) 400000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-691416124424702573) 25600000000000000000),
            (exactRationalLiteral (6931169562161451) 640000000000000000),
            (exactRationalLiteral (17415333036857769) 400000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2302710111647836147) 51200000000000000000),
            (exactRationalLiteral (-531408914502562467) 6400000000000000000),
            (exactRationalLiteral (-725146448404101) 6400000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (269794749742806551) 6144000000000000000),
            (exactRationalLiteral (406671859577375773) 6400000000000000000),
            (exactRationalLiteral (68029649538555383) 800000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-34455228842736437) 19200000000000000000),
            (exactRationalLiteral (-214067918721407) 400000000000000000),
            (exactRationalLiteral (-1379371872504911) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (-33664366700029997) 153600000000000000000),
            (exactRationalLiteral (-32585998187021303) 6400000000000000000),
            (exactRationalLiteral (-982963631504497) 160000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (10723638732477583) 1920000000000000000),
            (exactRationalLiteral (-764107593489037) 200000000000000000),
            (exactRationalLiteral (23447395435093) 10000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (3554049035438277167) 153600000000000000000),
            (exactRationalLiteral (-74434052143938299) 6400000000000000000),
            (exactRationalLiteral (614832635785867) 160000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-71011978807501967) 6400000000000000000),
            (exactRationalLiteral (1440572118397559) 160000000000000000),
            (exactRationalLiteral (-3499332908301) 800000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (-147373113063532581) 10240000000000000000),
            (exactRationalLiteral (1319353975635343) 256000000000000000),
            (exactRationalLiteral (-887997020612979) 800000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-42651132816222941) 10240000000000000000),
            (exactRationalLiteral (11816359351693391) 6400000000000000000),
            (exactRationalLiteral (23978783768613) 800000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3600266479233768491) 51200000000000000000),
            (exactRationalLiteral (195290000807666029) 6400000000000000000),
            (exactRationalLiteral (-6775508362697961) 800000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (11191185154519460467) 76800000000000000000),
            (exactRationalLiteral (-217420287008545383) 3200000000000000000),
            (exactRationalLiteral (7463424885091723) 400000000000000000),
            (exactRationalLiteral (-196301193326517) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-3600266479233768491) 51200000000000000000),
            (exactRationalLiteral (195290000807666029) 6400000000000000000),
            (exactRationalLiteral (-6775508362697961) 800000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-42651132816222941) 10240000000000000000),
            (exactRationalLiteral (11816359351693391) 6400000000000000000),
            (exactRationalLiteral (23978783768613) 800000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-147373113063532581) 10240000000000000000),
            (exactRationalLiteral (1319353975635343) 256000000000000000),
            (exactRationalLiteral (-887997020612979) 800000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-71011978807501967) 6400000000000000000),
            (exactRationalLiteral (1440572118397559) 160000000000000000),
            (exactRationalLiteral (-3499332908301) 800000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (3554049035438277167) 153600000000000000000),
            (exactRationalLiteral (-74434052143938299) 6400000000000000000),
            (exactRationalLiteral (614832635785867) 160000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (10723638732477583) 1920000000000000000),
            (exactRationalLiteral (-764107593489037) 200000000000000000),
            (exactRationalLiteral (23447395435093) 10000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-33664366700029997) 153600000000000000000),
            (exactRationalLiteral (-32585998187021303) 6400000000000000000),
            (exactRationalLiteral (-982963631504497) 160000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-34455228842736437) 19200000000000000000),
            (exactRationalLiteral (-214067918721407) 400000000000000000),
            (exactRationalLiteral (-1379371872504911) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (269794749742806551) 6144000000000000000),
            (exactRationalLiteral (406671859577375773) 6400000000000000000),
            (exactRationalLiteral (68029649538555383) 800000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2302710111647836147) 51200000000000000000),
            (exactRationalLiteral (-531408914502562467) 6400000000000000000),
            (exactRationalLiteral (-725146448404101) 6400000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-691416124424702573) 25600000000000000000),
            (exactRationalLiteral (6931169562161451) 640000000000000000),
            (exactRationalLiteral (17415333036857769) 400000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1381582934940256121) 76800000000000000000),
            (exactRationalLiteral (42651337177156991) 3200000000000000000),
            (exactRationalLiteral (3215266334253977) 400000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (903697414611020563) 76800000000000000000),
            (exactRationalLiteral (30240684486602053) 3200000000000000000),
            (exactRationalLiteral (-4661025053309741) 400000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-692643296971966801) 51200000000000000000),
            (exactRationalLiteral (-192689467249312929) 6400000000000000000),
            (exactRationalLiteral (22629988264279173) 800000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1984141983308284939) 51200000000000000000),
            (exactRationalLiteral (819521127989877147) 6400000000000000000),
            (exactRationalLiteral (-14775403191849927) 800000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (338702305243509967) 25600000000000000000),
            (exactRationalLiteral (-674112077893632629) 3200000000000000000),
            (exactRationalLiteral (-26986332629056563) 400000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3915803309821434457) 51200000000000000000),
            (exactRationalLiteral (792566966138526679) 6400000000000000000),
            (exactRationalLiteral (4347206945756853) 32000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (431082366124549833) 12800000000000000000),
            (exactRationalLiteral (-3205305068687023) 1600000000000000000),
            (exactRationalLiteral (-19008486263650509) 200000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (752865296771777) 245760000000000000),
            (exactRationalLiteral (-752865296771777) 51200000000000000),
            (exactRationalLiteral (752865296771777) 32000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (0 : ℚ),
          (exactRationalLiteral (6775787670945993) 1280000000000000000),
          (exactRationalLiteral (5503225377480997) 160000000000000000),
          (exactRationalLiteral (1718720050394687513) 19200000000000000000),
          (exactRationalLiteral (365898823482495877) 9600000000000000000),
          (exactRationalLiteral (26011802955833563) 480000000000000000),
          (exactRationalLiteral (40153440606696413) 2400000000000000000),
          (exactRationalLiteral (7635001843852001) 600000000000000000),
          (exactRationalLiteral (11876417452022903) 600000000000000000),
          (exactRationalLiteral (88797560653148497) 3200000000000000000),
          (exactRationalLiteral (137477004918729287) 2400000000000000000),
          (exactRationalLiteral (42649820235137957) 800000000000000000),
          (exactRationalLiteral (2541482066624383) 1200000000000000000),
          (exactRationalLiteral (2269729304325409) 2400000000000000000),
          (exactRationalLiteral (14644593310009711) 2400000000000000000),
          (exactRationalLiteral (473360072661308717) 19200000000000000000),
          (exactRationalLiteral (983312617099567) 80000000000000000),
          (exactRationalLiteral (289046606468479801) 19200000000000000000),
          (exactRationalLiteral (28124211435319539) 6400000000000000000),
          (exactRationalLiteral (1425950770322860391) 19200000000000000000),
          (exactRationalLiteral (1483303149222543917) 9600000000000000000),
          (exactRationalLiteral (1425950770322860391) 19200000000000000000),
          (exactRationalLiteral (28124211435319539) 6400000000000000000),
          (exactRationalLiteral (289046606468479801) 19200000000000000000),
          (exactRationalLiteral (983312617099567) 80000000000000000),
          (exactRationalLiteral (473360072661308717) 19200000000000000000),
          (exactRationalLiteral (14644593310009711) 2400000000000000000),
          (exactRationalLiteral (2269729304325409) 2400000000000000000),
          (exactRationalLiteral (2541482066624383) 1200000000000000000),
          (exactRationalLiteral (42649820235137957) 800000000000000000),
          (exactRationalLiteral (137477004918729287) 2400000000000000000),
          (exactRationalLiteral (88797560653148497) 3200000000000000000),
          (exactRationalLiteral (11876417452022903) 600000000000000000),
          (exactRationalLiteral (7635001843852001) 600000000000000000),
          (exactRationalLiteral (40153440606696413) 2400000000000000000),
          (exactRationalLiteral (26011802955833563) 480000000000000000),
          (exactRationalLiteral (365898823482495877) 9600000000000000000),
          (exactRationalLiteral (1718720050394687513) 19200000000000000000),
          (exactRationalLiteral (5503225377480997) 160000000000000000),
          (exactRationalLiteral (6775787670945993) 1280000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (43, 15),
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
      (42, 12)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 8
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (6775787670945993) 10240000000000000000),
            (exactRationalLiteral (-6775787670945993) 1280000000000000000),
            (exactRationalLiteral (2258595890315331) 160000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (217683807982667849) 7680000000000000000),
            (exactRationalLiteral (-57986446565480063) 1600000000000000000),
            (exactRationalLiteral (-8382084484746011) 200000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-6082325279231042029) 153600000000000000000),
            (exactRationalLiteral (1030048045551734663) 6400000000000000000),
            (exactRationalLiteral (10060366062682667) 800000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-622010606773123193) 15360000000000000000),
            (exactRationalLiteral (-660883153752694549) 3200000000000000000),
            (exactRationalLiteral (33600794699525603) 400000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (10349158451944348039) 153600000000000000000),
            (exactRationalLiteral (588874801413692171) 6400000000000000000),
            (exactRationalLiteral (-100547760096242561) 800000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2816201802900977989) 153600000000000000000),
            (exactRationalLiteral (-29016998022471281) 6400000000000000000),
            (exactRationalLiteral (59206246349141651) 800000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1003959965708185021) 76800000000000000000),
            (exactRationalLiteral (-205608663600479) 640000000000000000),
            (exactRationalLiteral (-10973338848992483) 400000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (561354553696595421) 25600000000000000000),
            (exactRationalLiteral (11901431210388627) 640000000000000000),
            (exactRationalLiteral (1042528620627819) 80000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-538652328443369651) 25600000000000000000),
            (exactRationalLiteral (25000666455333867) 640000000000000000),
            (exactRationalLiteral (27758409196073271) 400000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-11378234040132559951) 153600000000000000000),
            (exactRationalLiteral (-990947411488375571) 6400000000000000000),
            (exactRationalLiteral (-139125942442393927) 800000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (10159593409325327017) 153600000000000000000),
            (exactRationalLiteral (757959314645719309) 6400000000000000000),
            (exactRationalLiteral (21522815599123277) 160000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19954731694912127) 6400000000000000000),
            (exactRationalLiteral (-4544733850552261) 400000000000000000),
            (exactRationalLiteral (-2951294059325943) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (-18728336777183077) 10240000000000000000),
            (exactRationalLiteral (-48628709789770503) 6400000000000000000),
            (exactRationalLiteral (-621307528770423) 160000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (9133032317020511) 1920000000000000000),
            (exactRationalLiteral (-577279809518731) 200000000000000000),
            (exactRationalLiteral (69590806794841) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (3141879481653082057) 153600000000000000000),
            (exactRationalLiteral (-63364998962579627) 6400000000000000000),
            (exactRationalLiteral (2460363411750001) 800000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-58253897238173093) 6400000000000000000),
            (exactRationalLiteral (5606234397092971) 800000000000000000),
            (exactRationalLiteral (-360896483909787) 100000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (-404412926274432553) 30720000000000000000),
            (exactRationalLiteral (30074327549871783) 6400000000000000000),
            (exactRationalLiteral (-566763899892917) 800000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-189961855574518839) 51200000000000000000),
            (exactRationalLiteral (11260036488969791) 6400000000000000000),
            (exactRationalLiteral (-302140215130413) 800000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-9705483954243799351) 153600000000000000000),
            (exactRationalLiteral (6825150273552677) 256000000000000000),
            (exactRationalLiteral (-5555113621726591) 800000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (9971513302449452437) 76800000000000000000),
            (exactRationalLiteral (-37984440357619339) 640000000000000000),
            (exactRationalLiteral (6285617725132621) 400000000000000000),
            (exactRationalLiteral (-196301193326517) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-9705483954243799351) 153600000000000000000),
            (exactRationalLiteral (6825150273552677) 256000000000000000),
            (exactRationalLiteral (-5555113621726591) 800000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-189961855574518839) 51200000000000000000),
            (exactRationalLiteral (11260036488969791) 6400000000000000000),
            (exactRationalLiteral (-302140215130413) 800000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-404412926274432553) 30720000000000000000),
            (exactRationalLiteral (30074327549871783) 6400000000000000000),
            (exactRationalLiteral (-566763899892917) 800000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-58253897238173093) 6400000000000000000),
            (exactRationalLiteral (5606234397092971) 800000000000000000),
            (exactRationalLiteral (-360896483909787) 100000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (3141879481653082057) 153600000000000000000),
            (exactRationalLiteral (-63364998962579627) 6400000000000000000),
            (exactRationalLiteral (2460363411750001) 800000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9133032317020511) 1920000000000000000),
            (exactRationalLiteral (-577279809518731) 200000000000000000),
            (exactRationalLiteral (69590806794841) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-18728336777183077) 10240000000000000000),
            (exactRationalLiteral (-48628709789770503) 6400000000000000000),
            (exactRationalLiteral (-621307528770423) 160000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-19954731694912127) 6400000000000000000),
            (exactRationalLiteral (-4544733850552261) 400000000000000000),
            (exactRationalLiteral (-2951294059325943) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (10159593409325327017) 153600000000000000000),
            (exactRationalLiteral (757959314645719309) 6400000000000000000),
            (exactRationalLiteral (21522815599123277) 160000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-11378234040132559951) 153600000000000000000),
            (exactRationalLiteral (-990947411488375571) 6400000000000000000),
            (exactRationalLiteral (-139125942442393927) 800000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-538652328443369651) 25600000000000000000),
            (exactRationalLiteral (25000666455333867) 640000000000000000),
            (exactRationalLiteral (27758409196073271) 400000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (561354553696595421) 25600000000000000000),
            (exactRationalLiteral (11901431210388627) 640000000000000000),
            (exactRationalLiteral (1042528620627819) 80000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1003959965708185021) 76800000000000000000),
            (exactRationalLiteral (-205608663600479) 640000000000000000),
            (exactRationalLiteral (-10973338848992483) 400000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2816201802900977989) 153600000000000000000),
            (exactRationalLiteral (-29016998022471281) 6400000000000000000),
            (exactRationalLiteral (59206246349141651) 800000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (10349158451944348039) 153600000000000000000),
            (exactRationalLiteral (588874801413692171) 6400000000000000000),
            (exactRationalLiteral (-100547760096242561) 800000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-622010606773123193) 15360000000000000000),
            (exactRationalLiteral (-660883153752694549) 3200000000000000000),
            (exactRationalLiteral (33600794699525603) 400000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6082325279231042029) 153600000000000000000),
            (exactRationalLiteral (1030048045551734663) 6400000000000000000),
            (exactRationalLiteral (10060366062682667) 800000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (217683807982667849) 7680000000000000000),
            (exactRationalLiteral (-57986446565480063) 1600000000000000000),
            (exactRationalLiteral (-8382084484746011) 200000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (6775787670945993) 10240000000000000000),
            (exactRationalLiteral (-6775787670945993) 1280000000000000000),
            (exactRationalLiteral (2258595890315331) 160000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (0 : ℚ),
          (exactRationalLiteral (752865296771777) 480000000000000000),
          (exactRationalLiteral (19248733207282643) 600000000000000000),
          (exactRationalLiteral (142077787717305917) 2400000000000000000),
          (exactRationalLiteral (41346721228006931) 640000000000000000),
          (exactRationalLiteral (490468891560187523) 6400000000000000000),
          (exactRationalLiteral (12177971567979259) 640000000000000000),
          (exactRationalLiteral (6356633863356353) 480000000000000000),
          (exactRationalLiteral (234902718367434439) 9600000000000000000),
          (exactRationalLiteral (2490707412306647) 100000000000000000),
          (exactRationalLiteral (616362309171700379) 6400000000000000000),
          (exactRationalLiteral (63880529007389323) 768000000000000000),
          (exactRationalLiteral (24193110364859573) 4800000000000000000),
          (exactRationalLiteral (54403331712722353) 19200000000000000000),
          (exactRationalLiteral (1028363248912287) 200000000000000000),
          (exactRationalLiteral (17394075357602399) 800000000000000000),
          (exactRationalLiteral (2007305671066057) 200000000000000000),
          (exactRationalLiteral (33033570660653389) 2400000000000000000),
          (exactRationalLiteral (3147963736127123) 800000000000000000),
          (exactRationalLiteral (159916340046811181) 2400000000000000000),
          (exactRationalLiteral (165011338508892499) 1200000000000000000),
          (exactRationalLiteral (159916340046811181) 2400000000000000000),
          (exactRationalLiteral (3147963736127123) 800000000000000000),
          (exactRationalLiteral (33033570660653389) 2400000000000000000),
          (exactRationalLiteral (2007305671066057) 200000000000000000),
          (exactRationalLiteral (17394075357602399) 800000000000000000),
          (exactRationalLiteral (1028363248912287) 200000000000000000),
          (exactRationalLiteral (54403331712722353) 19200000000000000000),
          (exactRationalLiteral (24193110364859573) 4800000000000000000),
          (exactRationalLiteral (63880529007389323) 768000000000000000),
          (exactRationalLiteral (616362309171700379) 6400000000000000000),
          (exactRationalLiteral (2490707412306647) 100000000000000000),
          (exactRationalLiteral (234902718367434439) 9600000000000000000),
          (exactRationalLiteral (6356633863356353) 480000000000000000),
          (exactRationalLiteral (12177971567979259) 640000000000000000),
          (exactRationalLiteral (490468891560187523) 6400000000000000000),
          (exactRationalLiteral (41346721228006931) 640000000000000000),
          (exactRationalLiteral (142077787717305917) 2400000000000000000),
          (exactRationalLiteral (19248733207282643) 600000000000000000),
          (exactRationalLiteral (752865296771777) 480000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (43, 16),
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
      (42, 11)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 8
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (752865296771777) 30720000000000000000),
            (exactRationalLiteral (-752865296771777) 1280000000000000000),
            (exactRationalLiteral (752865296771777) 160000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (682420953819124727) 38400000000000000000),
            (exactRationalLiteral (-70261980946655111) 1600000000000000000),
            (exactRationalLiteral (2244317294158487) 200000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-175791843493396679) 153600000000000000000),
            (exactRationalLiteral (174609978927997603) 1280000000000000000),
            (exactRationalLiteral (-88559441518555991) 800000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6429793910673147359) 76800000000000000000),
            (exactRationalLiteral (-81061144059485561) 640000000000000000),
            (exactRationalLiteral (94187922028107769) 400000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (12332744711654019797) 153600000000000000000),
            (exactRationalLiteral (15139047219936659) 6400000000000000000),
            (exactRationalLiteral (-37264023400127039) 160000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2133523802506655951) 153600000000000000000),
            (exactRationalLiteral (280960503543820279) 6400000000000000000),
            (exactRationalLiteral (95782504434004129) 800000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (840862384429529887) 76800000000000000000),
            (exactRationalLiteral (-57546026305337811) 3200000000000000000),
            (exactRationalLiteral (-691426105787009) 16000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (422329564342930937) 15360000000000000000),
            (exactRationalLiteral (84352482002269751) 3200000000000000000),
            (exactRationalLiteral (7210019872024213) 400000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-163821258893450561) 25600000000000000000),
            (exactRationalLiteral (256723121379393423) 3200000000000000000),
            (exactRationalLiteral (38101485355288773) 400000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-19187360363939065709) 153600000000000000000),
            (exactRationalLiteral (-1644416454041713883) 6400000000000000000),
            (exactRationalLiteral (-187608578834275229) 800000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5385685315658427833) 51200000000000000000),
            (exactRationalLiteral (1267584483542306853) 6400000000000000000),
            (exactRationalLiteral (147198506452677387) 800000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-156104218750558957) 19200000000000000000),
            (exactRationalLiteral (-12019244156025179) 400000000000000000),
            (exactRationalLiteral (-180928649845879) 4000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (-602742640067913073) 153600000000000000000),
            (exactRationalLiteral (-57438299337838223) 6400000000000000000),
            (exactRationalLiteral (-259651426036349) 160000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (13127436290297793) 3200000000000000000),
            (exactRationalLiteral (-485744366309673) 200000000000000000),
            (exactRationalLiteral (21944636414217) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (929586216583295657) 51200000000000000000),
            (exactRationalLiteral (-54751144849938291) 6400000000000000000),
            (exactRationalLiteral (1846563644570667) 800000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9676597508024503) 1280000000000000000),
            (exactRationalLiteral (4315688720709499) 800000000000000000),
            (exactRationalLiteral (-284376354281949) 100000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (-1847134900388766823) 153600000000000000000),
            (exactRationalLiteral (28449738191740239) 6400000000000000000),
            (exactRationalLiteral (-49106155834571) 160000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-169085168788966277) 51200000000000000000),
            (exactRationalLiteral (9399237630650087) 6400000000000000000),
            (exactRationalLiteral (-628259214029439) 800000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-8743491197707731413) 153600000000000000000),
            (exactRationalLiteral (150849091833853301) 6400000000000000000),
            (exactRationalLiteral (-4334718880755221) 800000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (8902696275782627311) 76800000000000000000),
            (exactRationalLiteral (-33427069041496883) 640000000000000000),
            (exactRationalLiteral (5107810565173519) 400000000000000000),
            (exactRationalLiteral (-196301193326517) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-8743491197707731413) 153600000000000000000),
            (exactRationalLiteral (150849091833853301) 6400000000000000000),
            (exactRationalLiteral (-4334718880755221) 800000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-169085168788966277) 51200000000000000000),
            (exactRationalLiteral (9399237630650087) 6400000000000000000),
            (exactRationalLiteral (-628259214029439) 800000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1847134900388766823) 153600000000000000000),
            (exactRationalLiteral (28449738191740239) 6400000000000000000),
            (exactRationalLiteral (-49106155834571) 160000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9676597508024503) 1280000000000000000),
            (exactRationalLiteral (4315688720709499) 800000000000000000),
            (exactRationalLiteral (-284376354281949) 100000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (929586216583295657) 51200000000000000000),
            (exactRationalLiteral (-54751144849938291) 6400000000000000000),
            (exactRationalLiteral (1846563644570667) 800000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (13127436290297793) 3200000000000000000),
            (exactRationalLiteral (-485744366309673) 200000000000000000),
            (exactRationalLiteral (21944636414217) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-602742640067913073) 153600000000000000000),
            (exactRationalLiteral (-57438299337838223) 6400000000000000000),
            (exactRationalLiteral (-259651426036349) 160000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-156104218750558957) 19200000000000000000),
            (exactRationalLiteral (-12019244156025179) 400000000000000000),
            (exactRationalLiteral (-180928649845879) 4000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (5385685315658427833) 51200000000000000000),
            (exactRationalLiteral (1267584483542306853) 6400000000000000000),
            (exactRationalLiteral (147198506452677387) 800000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19187360363939065709) 153600000000000000000),
            (exactRationalLiteral (-1644416454041713883) 6400000000000000000),
            (exactRationalLiteral (-187608578834275229) 800000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-163821258893450561) 25600000000000000000),
            (exactRationalLiteral (256723121379393423) 3200000000000000000),
            (exactRationalLiteral (38101485355288773) 400000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (422329564342930937) 15360000000000000000),
            (exactRationalLiteral (84352482002269751) 3200000000000000000),
            (exactRationalLiteral (7210019872024213) 400000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (840862384429529887) 76800000000000000000),
            (exactRationalLiteral (-57546026305337811) 3200000000000000000),
            (exactRationalLiteral (-691426105787009) 16000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2133523802506655951) 153600000000000000000),
            (exactRationalLiteral (280960503543820279) 6400000000000000000),
            (exactRationalLiteral (95782504434004129) 800000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (12332744711654019797) 153600000000000000000),
            (exactRationalLiteral (15139047219936659) 6400000000000000000),
            (exactRationalLiteral (-37264023400127039) 160000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6429793910673147359) 76800000000000000000),
            (exactRationalLiteral (-81061144059485561) 640000000000000000),
            (exactRationalLiteral (94187922028107769) 400000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-175791843493396679) 153600000000000000000),
            (exactRationalLiteral (174609978927997603) 1280000000000000000),
            (exactRationalLiteral (-88559441518555991) 800000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (682420953819124727) 38400000000000000000),
            (exactRationalLiteral (-70261980946655111) 1600000000000000000),
            (exactRationalLiteral (2244317294158487) 200000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (752865296771777) 30720000000000000000),
            (exactRationalLiteral (-752865296771777) 1280000000000000000),
            (exactRationalLiteral (752865296771777) 160000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (0 : ℚ),
          (exactRationalLiteral (752865296771777) 3840000000000000000),
          (exactRationalLiteral (37276110318838053) 1600000000000000000),
          (exactRationalLiteral (125471247840767057) 6400000000000000000),
          (exactRationalLiteral (28643959928971939) 300000000000000000),
          (exactRationalLiteral (32752838683142677) 400000000000000000),
          (exactRationalLiteral (22561216073987797) 1280000000000000000),
          (exactRationalLiteral (120599957788669877) 9600000000000000000),
          (exactRationalLiteral (3108507832971327) 100000000000000000),
          (exactRationalLiteral (48020842618011391) 3200000000000000000),
          (exactRationalLiteral (48257181212427683) 300000000000000000),
          (exactRationalLiteral (1994257532342653) 15000000000000000),
          (exactRationalLiteral (1263412987075841) 100000000000000000),
          (exactRationalLiteral (126635444208193) 25000000000000000),
          (exactRationalLiteral (2119321603159219) 480000000000000000),
          (exactRationalLiteral (369857334389625439) 19200000000000000000),
          (exactRationalLiteral (1656118936564123) 200000000000000000),
          (exactRationalLiteral (80557555160911089) 6400000000000000000),
          (exactRationalLiteral (22382289058395329) 6400000000000000000),
          (exactRationalLiteral (383735534467585111) 6400000000000000000),
          (exactRationalLiteral (1177501830835072583) 9600000000000000000),
          (exactRationalLiteral (383735534467585111) 6400000000000000000),
          (exactRationalLiteral (22382289058395329) 6400000000000000000),
          (exactRationalLiteral (80557555160911089) 6400000000000000000),
          (exactRationalLiteral (1656118936564123) 200000000000000000),
          (exactRationalLiteral (369857334389625439) 19200000000000000000),
          (exactRationalLiteral (2119321603159219) 480000000000000000),
          (exactRationalLiteral (126635444208193) 25000000000000000),
          (exactRationalLiteral (1263412987075841) 100000000000000000),
          (exactRationalLiteral (1994257532342653) 15000000000000000),
          (exactRationalLiteral (48257181212427683) 300000000000000000),
          (exactRationalLiteral (48020842618011391) 3200000000000000000),
          (exactRationalLiteral (3108507832971327) 100000000000000000),
          (exactRationalLiteral (120599957788669877) 9600000000000000000),
          (exactRationalLiteral (22561216073987797) 1280000000000000000),
          (exactRationalLiteral (32752838683142677) 400000000000000000),
          (exactRationalLiteral (28643959928971939) 300000000000000000),
          (exactRationalLiteral (125471247840767057) 6400000000000000000),
          (exactRationalLiteral (37276110318838053) 1600000000000000000),
          (exactRationalLiteral (752865296771777) 3840000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (43, 17),
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
      (42, 10)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 8
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (6775787670945993) 655360000000000000),
            (exactRationalLiteral (-6775787670945993) 204800000000000000),
            (exactRationalLiteral (2258595890315331) 64000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (7022872040381309897) 307200000000000000000),
            (exactRationalLiteral (500178527234568313) 6400000000000000000),
            (exactRationalLiteral (-64582976974562263) 400000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-119067533383610412833) 1228800000000000000000),
            (exactRationalLiteral (-236083203089803009) 25600000000000000000),
            (exactRationalLiteral (92781973248187859) 320000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (40740934647067327123) 614400000000000000000),
            (exactRationalLiteral (-1399382567386122181) 12800000000000000000),
            (exactRationalLiteral (-205440483579568541) 800000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1592601747753260291) 1228800000000000000000),
            (exactRationalLiteral (2501438114491599203) 25600000000000000000),
            (exactRationalLiteral (184880085877281731) 1600000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3953588983030456409) 1228800000000000000000),
            (exactRationalLiteral (-766154408222054201) 25600000000000000000),
            (exactRationalLiteral (-46180668683597849) 1600000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5110504101925751549) 614400000000000000000),
            (exactRationalLiteral (135279316566568757) 12800000000000000000),
            (exactRationalLiteral (6458734382587373) 800000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2950345716991802061) 204800000000000000000),
            (exactRationalLiteral (131267231634612399) 12800000000000000000),
            (exactRationalLiteral (1437090746295159) 800000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5569160053087866859) 204800000000000000000),
            (exactRationalLiteral (-16078963500746517) 2560000000000000000),
            (exactRationalLiteral (8972975675676783) 800000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-33946838942478631883) 1228800000000000000000),
            (exactRationalLiteral (-918802491898513643) 25600000000000000000),
            (exactRationalLiteral (-12016004224264399) 320000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7457811805227151729) 245760000000000000000),
            (exactRationalLiteral (760899803251657957) 25600000000000000000),
            (exactRationalLiteral (37098227934458261) 1600000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-59769054115790801) 25600000000000000000),
            (exactRationalLiteral (48639584102063) 25000000000000000),
            (exactRationalLiteral (585530861021379) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (278534900629422443) 409600000000000000000),
            (exactRationalLiteral (-9444123176755887) 25600000000000000000),
            (exactRationalLiteral (-2870067519844179) 320000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (54120189274289651) 7680000000000000000),
            (exactRationalLiteral (-2263294355294849) 400000000000000000),
            (exactRationalLiteral (35358938030249) 10000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (33397922374430623901) 1228800000000000000000),
            (exactRationalLiteral (-366891969244081571) 25600000000000000000),
            (exactRationalLiteral (1536565155161401) 320000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-735618042343899511) 51200000000000000000),
            (exactRationalLiteral (7703255251810331) 640000000000000000),
            (exactRationalLiteral (-213226710228969) 40000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (-3963416230842774989) 245760000000000000000),
            (exactRationalLiteral (30742150396958931) 5120000000000000000),
            (exactRationalLiteral (-2579076843026113) 1600000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-386875882936791687) 81920000000000000000),
            (exactRationalLiteral (42709374245163479) 25600000000000000000),
            (exactRationalLiteral (863255064784791) 1600000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-99216396475785810299) 1228800000000000000000),
            (exactRationalLiteral (931925104746765461) 25600000000000000000),
            (exactRationalLiteral (-16602003577824347) 1600000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (103767825136929609041) 614400000000000000000),
            (exactRationalLiteral (-1033672235235504767) 12800000000000000000),
            (exactRationalLiteral (17871367670081201) 800000000000000000),
            (exactRationalLiteral (-196301193326517) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-99216396475785810299) 1228800000000000000000),
            (exactRationalLiteral (931925104746765461) 25600000000000000000),
            (exactRationalLiteral (-16602003577824347) 1600000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-386875882936791687) 81920000000000000000),
            (exactRationalLiteral (42709374245163479) 25600000000000000000),
            (exactRationalLiteral (863255064784791) 1600000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3963416230842774989) 245760000000000000000),
            (exactRationalLiteral (30742150396958931) 5120000000000000000),
            (exactRationalLiteral (-2579076843026113) 1600000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-735618042343899511) 51200000000000000000),
            (exactRationalLiteral (7703255251810331) 640000000000000000),
            (exactRationalLiteral (-213226710228969) 40000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (33397922374430623901) 1228800000000000000000),
            (exactRationalLiteral (-366891969244081571) 25600000000000000000),
            (exactRationalLiteral (1536565155161401) 320000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (54120189274289651) 7680000000000000000),
            (exactRationalLiteral (-2263294355294849) 400000000000000000),
            (exactRationalLiteral (35358938030249) 10000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (278534900629422443) 409600000000000000000),
            (exactRationalLiteral (-9444123176755887) 25600000000000000000),
            (exactRationalLiteral (-2870067519844179) 320000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-59769054115790801) 25600000000000000000),
            (exactRationalLiteral (48639584102063) 25000000000000000),
            (exactRationalLiteral (585530861021379) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (7457811805227151729) 245760000000000000000),
            (exactRationalLiteral (760899803251657957) 25600000000000000000),
            (exactRationalLiteral (37098227934458261) 1600000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-33946838942478631883) 1228800000000000000000),
            (exactRationalLiteral (-918802491898513643) 25600000000000000000),
            (exactRationalLiteral (-12016004224264399) 320000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5569160053087866859) 204800000000000000000),
            (exactRationalLiteral (-16078963500746517) 2560000000000000000),
            (exactRationalLiteral (8972975675676783) 800000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2950345716991802061) 204800000000000000000),
            (exactRationalLiteral (131267231634612399) 12800000000000000000),
            (exactRationalLiteral (1437090746295159) 800000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5110504101925751549) 614400000000000000000),
            (exactRationalLiteral (135279316566568757) 12800000000000000000),
            (exactRationalLiteral (6458734382587373) 800000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-3953588983030456409) 1228800000000000000000),
            (exactRationalLiteral (-766154408222054201) 25600000000000000000),
            (exactRationalLiteral (-46180668683597849) 1600000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1592601747753260291) 1228800000000000000000),
            (exactRationalLiteral (2501438114491599203) 25600000000000000000),
            (exactRationalLiteral (184880085877281731) 1600000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (40740934647067327123) 614400000000000000000),
            (exactRationalLiteral (-1399382567386122181) 12800000000000000000),
            (exactRationalLiteral (-205440483579568541) 800000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-119067533383610412833) 1228800000000000000000),
            (exactRationalLiteral (-236083203089803009) 25600000000000000000),
            (exactRationalLiteral (92781973248187859) 320000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7022872040381309897) 307200000000000000000),
            (exactRationalLiteral (500178527234568313) 6400000000000000000),
            (exactRationalLiteral (-64582976974562263) 400000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (6775787670945993) 655360000000000000),
            (exactRationalLiteral (-6775787670945993) 204800000000000000),
            (exactRationalLiteral (2258595890315331) 64000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (0 : ℚ),
          (exactRationalLiteral (752865296771777) 60000000000000000),
          (exactRationalLiteral (1041871486506347537) 38400000000000000000),
          (exactRationalLiteral (935298566790238561) 9600000000000000000),
          (exactRationalLiteral (1441812087722093) 20000000000000000),
          (exactRationalLiteral (1201083771300963347) 153600000000000000000),
          (exactRationalLiteral (159307652117624533) 30720000000000000000),
          (exactRationalLiteral (691570262234422321) 76800000000000000000),
          (exactRationalLiteral (1156268600812821427) 76800000000000000000),
          (exactRationalLiteral (704857256111173343) 25600000000000000000),
          (exactRationalLiteral (4613465974966759931) 153600000000000000000),
          (exactRationalLiteral (66171408889871063) 2048000000000000000),
          (exactRationalLiteral (728501520957809) 300000000000000000),
          (exactRationalLiteral (1680279888517733) 2400000000000000000),
          (exactRationalLiteral (222439850090833) 30000000000000000),
          (exactRationalLiteral (263381604456893) 9375000000000000),
          (exactRationalLiteral (189261036501229) 12500000000000000),
          (exactRationalLiteral (165088796038881) 10000000000000000),
          (exactRationalLiteral (241231833581281) 50000000000000000),
          (exactRationalLiteral (8305874674326991) 100000000000000000),
          (exactRationalLiteral (26104258996393151) 150000000000000000),
          (exactRationalLiteral (8305874674326991) 100000000000000000),
          (exactRationalLiteral (241231833581281) 50000000000000000),
          (exactRationalLiteral (165088796038881) 10000000000000000),
          (exactRationalLiteral (189261036501229) 12500000000000000),
          (exactRationalLiteral (263381604456893) 9375000000000000),
          (exactRationalLiteral (222439850090833) 30000000000000000),
          (exactRationalLiteral (1680279888517733) 2400000000000000000),
          (exactRationalLiteral (728501520957809) 300000000000000000),
          (exactRationalLiteral (66171408889871063) 2048000000000000000),
          (exactRationalLiteral (4613465974966759931) 153600000000000000000),
          (exactRationalLiteral (704857256111173343) 25600000000000000000),
          (exactRationalLiteral (1156268600812821427) 76800000000000000000),
          (exactRationalLiteral (691570262234422321) 76800000000000000000),
          (exactRationalLiteral (159307652117624533) 30720000000000000000),
          (exactRationalLiteral (1201083771300963347) 153600000000000000000),
          (exactRationalLiteral (1441812087722093) 20000000000000000),
          (exactRationalLiteral (935298566790238561) 9600000000000000000),
          (exactRationalLiteral (1041871486506347537) 38400000000000000000),
          (exactRationalLiteral (752865296771777) 60000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (39, 4),
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
      (37, 3)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 8
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (1654045057007594069) 245760000000000000000),
            (exactRationalLiteral (-127234235154430313) 5120000000000000000),
            (exactRationalLiteral (9787248858033101) 320000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (3097151029069863537) 102400000000000000000),
            (exactRationalLiteral (263099422894128257) 6400000000000000000),
            (exactRationalLiteral (-10791315039131553) 80000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-38437197812527637993) 409600000000000000000),
            (exactRationalLiteral (284463329342295371) 5120000000000000000),
            (exactRationalLiteral (365290058659700637) 1600000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (10040567316370033403) 204800000000000000000),
            (exactRationalLiteral (-2099970247047232013) 12800000000000000000),
            (exactRationalLiteral (-1158826850007891) 6400000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1231780135840844383) 81920000000000000000),
            (exactRationalLiteral (3069413744191940859) 25600000000000000000),
            (exactRationalLiteral (99107728972889097) 1600000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2986126141408835297) 409600000000000000000),
            (exactRationalLiteral (-877724566786720641) 25600000000000000000),
            (exactRationalLiteral (-9604410598735371) 1600000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5974435558733481599) 614400000000000000000),
            (exactRationalLiteral (29697925301110553) 2560000000000000000),
            (exactRationalLiteral (146420586904631) 800000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (9663875136814162957) 614400000000000000000),
            (exactRationalLiteral (141010348157563271) 12800000000000000000),
            (exactRationalLiteral (3434467515180277) 800000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5680267017180337561) 204800000000000000000),
            (exactRationalLiteral (-23816762482594449) 12800000000000000000),
            (exactRationalLiteral (3863210366978457) 160000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-13458181564297700963) 409600000000000000000),
            (exactRationalLiteral (-1256087849167564227) 25600000000000000000),
            (exactRationalLiteral (-108562657513203297) 1600000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (42457974294687449527) 1228800000000000000000),
            (exactRationalLiteral (197692314380722601) 5120000000000000000),
            (exactRationalLiteral (76682656391519263) 1600000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-156747036093565727) 76800000000000000000),
            (exactRationalLiteral (970783659949129) 400000000000000000),
            (exactRationalLiteral (-200430232389137) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (613969033691762747) 1228800000000000000000),
            (exactRationalLiteral (-63228912546298727) 25600000000000000000),
            (exactRationalLiteral (-501682283422021) 64000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (245467658048963759) 38400000000000000000),
            (exactRationalLiteral (-1933528060182671) 400000000000000000),
            (exactRationalLiteral (152971604960933) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (31286309269207101199) 1228800000000000000000),
            (exactRationalLiteral (-337388265675212219) 25600000000000000000),
            (exactRationalLiteral (7069026008627671) 1600000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-662747997190871797) 51200000000000000000),
            (exactRationalLiteral (34404782313727951) 3200000000000000000),
            (exactRationalLiteral (-989613421517007) 200000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (-6308160210646180041) 409600000000000000000),
            (exactRationalLiteral (144036910854130327) 25600000000000000000),
            (exactRationalLiteral (-2257843722306051) 1600000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1845942471266357681) 409600000000000000000),
            (exactRationalLiteral (45510156506504591) 25600000000000000000),
            (exactRationalLiteral (107427213177153) 320000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-31273062770425074739) 409600000000000000000),
            (exactRationalLiteral (867957879917410813) 25600000000000000000),
            (exactRationalLiteral (-15381608836852977) 1600000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (97775536908917718443) 614400000000000000000),
            (exactRationalLiteral (-964542378875098167) 12800000000000000000),
            (exactRationalLiteral (16693560510122099) 800000000000000000),
            (exactRationalLiteral (-196301193326517) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-31273062770425074739) 409600000000000000000),
            (exactRationalLiteral (867957879917410813) 25600000000000000000),
            (exactRationalLiteral (-15381608836852977) 1600000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-1845942471266357681) 409600000000000000000),
            (exactRationalLiteral (45510156506504591) 25600000000000000000),
            (exactRationalLiteral (107427213177153) 320000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-6308160210646180041) 409600000000000000000),
            (exactRationalLiteral (144036910854130327) 25600000000000000000),
            (exactRationalLiteral (-2257843722306051) 1600000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-662747997190871797) 51200000000000000000),
            (exactRationalLiteral (34404782313727951) 3200000000000000000),
            (exactRationalLiteral (-989613421517007) 200000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (31286309269207101199) 1228800000000000000000),
            (exactRationalLiteral (-337388265675212219) 25600000000000000000),
            (exactRationalLiteral (7069026008627671) 1600000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (245467658048963759) 38400000000000000000),
            (exactRationalLiteral (-1933528060182671) 400000000000000000),
            (exactRationalLiteral (152971604960933) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (613969033691762747) 1228800000000000000000),
            (exactRationalLiteral (-63228912546298727) 25600000000000000000),
            (exactRationalLiteral (-501682283422021) 64000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-156747036093565727) 76800000000000000000),
            (exactRationalLiteral (970783659949129) 400000000000000000),
            (exactRationalLiteral (-200430232389137) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (42457974294687449527) 1228800000000000000000),
            (exactRationalLiteral (197692314380722601) 5120000000000000000),
            (exactRationalLiteral (76682656391519263) 1600000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-13458181564297700963) 409600000000000000000),
            (exactRationalLiteral (-1256087849167564227) 25600000000000000000),
            (exactRationalLiteral (-108562657513203297) 1600000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5680267017180337561) 204800000000000000000),
            (exactRationalLiteral (-23816762482594449) 12800000000000000000),
            (exactRationalLiteral (3863210366978457) 160000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (9663875136814162957) 614400000000000000000),
            (exactRationalLiteral (141010348157563271) 12800000000000000000),
            (exactRationalLiteral (3434467515180277) 800000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5974435558733481599) 614400000000000000000),
            (exactRationalLiteral (29697925301110553) 2560000000000000000),
            (exactRationalLiteral (146420586904631) 800000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2986126141408835297) 409600000000000000000),
            (exactRationalLiteral (-877724566786720641) 25600000000000000000),
            (exactRationalLiteral (-9604410598735371) 1600000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1231780135840844383) 81920000000000000000),
            (exactRationalLiteral (3069413744191940859) 25600000000000000000),
            (exactRationalLiteral (99107728972889097) 1600000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (10040567316370033403) 204800000000000000000),
            (exactRationalLiteral (-2099970247047232013) 12800000000000000000),
            (exactRationalLiteral (-1158826850007891) 6400000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-38437197812527637993) 409600000000000000000),
            (exactRationalLiteral (284463329342295371) 5120000000000000000),
            (exactRationalLiteral (365290058659700637) 1600000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3097151029069863537) 102400000000000000000),
            (exactRationalLiteral (263099422894128257) 6400000000000000000),
            (exactRationalLiteral (-10791315039131553) 80000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1654045057007594069) 245760000000000000000),
            (exactRationalLiteral (-127234235154430313) 5120000000000000000),
            (exactRationalLiteral (9787248858033101) 320000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (0 : ℚ),
          (exactRationalLiteral (258232796792719511) 30720000000000000000),
          (exactRationalLiteral (155065544237413349) 4800000000000000000),
          (exactRationalLiteral (14804170412243452913) 153600000000000000000),
          (exactRationalLiteral (898918976445863651) 15360000000000000000),
          (exactRationalLiteral (436552816853983739) 19200000000000000000),
          (exactRationalLiteral (181282456677194417) 19200000000000000000),
          (exactRationalLiteral (100268555361140819) 9600000000000000000),
          (exactRationalLiteral (10518966950225871) 640000000000000000),
          (exactRationalLiteral (178011514624355283) 6400000000000000000),
          (exactRationalLiteral (695199023923927283) 19200000000000000000),
          (exactRationalLiteral (713643737403146513) 19200000000000000000),
          (exactRationalLiteral (42151187540854357) 19200000000000000000),
          (exactRationalLiteral (95640682477146521) 153600000000000000000),
          (exactRationalLiteral (4292327546125629) 640000000000000000),
          (exactRationalLiteral (1346666168505925439) 51200000000000000000),
          (exactRationalLiteral (87269393285131841) 6400000000000000000),
          (exactRationalLiteral (2420440689028526161) 153600000000000000000),
          (exactRationalLiteral (236357642317561667) 51200000000000000000),
          (exactRationalLiteral (12058727121863562659) 153600000000000000000),
          (exactRationalLiteral (12589979203831669849) 76800000000000000000),
          (exactRationalLiteral (12058727121863562659) 153600000000000000000),
          (exactRationalLiteral (236357642317561667) 51200000000000000000),
          (exactRationalLiteral (2420440689028526161) 153600000000000000000),
          (exactRationalLiteral (87269393285131841) 6400000000000000000),
          (exactRationalLiteral (1346666168505925439) 51200000000000000000),
          (exactRationalLiteral (4292327546125629) 640000000000000000),
          (exactRationalLiteral (95640682477146521) 153600000000000000000),
          (exactRationalLiteral (42151187540854357) 19200000000000000000),
          (exactRationalLiteral (713643737403146513) 19200000000000000000),
          (exactRationalLiteral (695199023923927283) 19200000000000000000),
          (exactRationalLiteral (178011514624355283) 6400000000000000000),
          (exactRationalLiteral (10518966950225871) 640000000000000000),
          (exactRationalLiteral (100268555361140819) 9600000000000000000),
          (exactRationalLiteral (181282456677194417) 19200000000000000000),
          (exactRationalLiteral (436552816853983739) 19200000000000000000),
          (exactRationalLiteral (898918976445863651) 15360000000000000000),
          (exactRationalLiteral (14804170412243452913) 153600000000000000000),
          (exactRationalLiteral (155065544237413349) 4800000000000000000),
          (exactRationalLiteral (258232796792719511) 30720000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (39, 5),
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
      (37, 2)
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
      true
    ]
  },
  {
    cubic :=
      {
        cell := 8
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
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (exactRationalLiteral (1002063710003235187) 245760000000000000000),
            (exactRationalLiteral (-91096700909385017) 5120000000000000000),
            (exactRationalLiteral (8281518264489547) 320000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (2053015265868416993) 61440000000000000000),
            (exactRationalLiteral (68525925669306193) 6400000000000000000),
            (exactRationalLiteral (-43330173416753267) 400000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-102788692083722599837) 1228800000000000000000),
            (exactRationalLiteral (2686237266187802087) 25600000000000000000),
            (exactRationalLiteral (266670251078461979) 1600000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3205197740225840059) 122880000000000000000),
            (exactRationalLiteral (-2558209417394013181) 12800000000000000000),
            (exactRationalLiteral (-84266228922404209) 800000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (37739387822821409527) 1228800000000000000000),
            (exactRationalLiteral (3294299946274711979) 25600000000000000000),
            (exactRationalLiteral (13335372068496463) 1600000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-14193673719792204277) 1228800000000000000000),
            (exactRationalLiteral (-842989693011937169) 25600000000000000000),
            (exactRationalLiteral (26971847486127107) 1600000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6841881109626922793) 614400000000000000000),
            (exactRationalLiteral (27290136252361161) 2560000000000000000),
            (exactRationalLiteral (-6165893208778111) 800000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (10559140343017246379) 614400000000000000000),
            (exactRationalLiteral (31748594351210923) 2560000000000000000),
            (exactRationalLiteral (1086368856813079) 160000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5636845566593669983) 204800000000000000000),
            (exactRationalLiteral (14826719435081139) 2560000000000000000),
            (exactRationalLiteral (29659127994107787) 800000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-49407754223624453023) 1228800000000000000000),
            (exactRationalLiteral (-1787303752004140019) 25600000000000000000),
            (exactRationalLiteral (-157045293905084599) 1600000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (16489091105545200907) 409600000000000000000),
            (exactRationalLiteral (1374361054383812061) 25600000000000000000),
            (exactRationalLiteral (23253416969716053) 320000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-138997235417098339) 76800000000000000000),
            (exactRationalLiteral (188686440427367) 200000000000000000),
            (exactRationalLiteral (-986391325799653) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (18264799088409113) 245760000000000000000),
            (exactRationalLiteral (-109780579861160087) 25600000000000000000),
            (exactRationalLiteral (-2146755314376031) 320000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (14933712549702777) 2560000000000000000),
            (exactRationalLiteral (-1651407935451117) 400000000000000000),
            (exactRationalLiteral (129148519770621) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (9781450929396880867) 409600000000000000000),
            (exactRationalLiteral (-310339761175060203) 25600000000000000000),
            (exactRationalLiteral (6455226241448337) 1600000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-597794859409980139) 51200000000000000000),
            (exactRationalLiteral (30599368886915599) 3200000000000000000),
            (exactRationalLiteral (-913093291889169) 200000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (-723442734359942021) 49152000000000000000),
            (exactRationalLiteral (135648002206346247) 25600000000000000000),
            (exactRationalLiteral (-1936610601585989) 1600000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1753208439321670807) 409600000000000000000),
            (exactRationalLiteral (47006462772249599) 25600000000000000000),
            (exactRationalLiteral (211017066986739) 1600000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-88791138758849109583) 1228800000000000000000),
            (exactRationalLiteral (161774446810388329) 5120000000000000000),
            (exactRationalLiteral (-14161214095881607) 1600000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (92183894133148758221) 614400000000000000000),
            (exactRationalLiteral (-36004950046181119) 512000000000000000),
            (exactRationalLiteral (15515753350162997) 800000000000000000),
            (exactRationalLiteral (-196301193326517) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-88791138758849109583) 1228800000000000000000),
            (exactRationalLiteral (161774446810388329) 5120000000000000000),
            (exactRationalLiteral (-14161214095881607) 1600000000000000000),
            (exactRationalLiteral (122039474097137) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-1753208439321670807) 409600000000000000000),
            (exactRationalLiteral (47006462772249599) 25600000000000000000),
            (exactRationalLiteral (211017066986739) 1600000000000000000),
            (exactRationalLiteral (-54353166483171) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-723442734359942021) 49152000000000000000),
            (exactRationalLiteral (135648002206346247) 25600000000000000000),
            (exactRationalLiteral (-1936610601585989) 1600000000000000000),
            (exactRationalLiteral (160616560360031) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-597794859409980139) 51200000000000000000),
            (exactRationalLiteral (30599368886915599) 3200000000000000000),
            (exactRationalLiteral (-913093291889169) 200000000000000000),
            (exactRationalLiteral (12753354937973) 12500000000000000)
          ],
          ![
            (exactRationalLiteral (9781450929396880867) 409600000000000000000),
            (exactRationalLiteral (-310339761175060203) 25600000000000000000),
            (exactRationalLiteral (6455226241448337) 1600000000000000000),
            (exactRationalLiteral (-306899883589667) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (14933712549702777) 2560000000000000000),
            (exactRationalLiteral (-1651407935451117) 400000000000000000),
            (exactRationalLiteral (129148519770621) 50000000000000000),
            (exactRationalLiteral (-2977885648789) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (18264799088409113) 245760000000000000000),
            (exactRationalLiteral (-109780579861160087) 25600000000000000000),
            (exactRationalLiteral (-2146755314376031) 320000000000000000),
            (exactRationalLiteral (180828051367037) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-138997235417098339) 76800000000000000000),
            (exactRationalLiteral (188686440427367) 200000000000000000),
            (exactRationalLiteral (-986391325799653) 100000000000000000),
            (exactRationalLiteral (-196490273352629) 9375000000000000)
          ],
          ![
            (exactRationalLiteral (16489091105545200907) 409600000000000000000),
            (exactRationalLiteral (1374361054383812061) 25600000000000000000),
            (exactRationalLiteral (23253416969716053) 320000000000000000),
            (exactRationalLiteral (19792214228530501) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-49407754223624453023) 1228800000000000000000),
            (exactRationalLiteral (-1787303752004140019) 25600000000000000000),
            (exactRationalLiteral (-157045293905084599) 1600000000000000000),
            (exactRationalLiteral (-24241318195940651) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5636845566593669983) 204800000000000000000),
            (exactRationalLiteral (14826719435081139) 2560000000000000000),
            (exactRationalLiteral (29659127994107787) 800000000000000000),
            (exactRationalLiteral (1723846026535917) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (10559140343017246379) 614400000000000000000),
            (exactRationalLiteral (31748594351210923) 2560000000000000000),
            (exactRationalLiteral (1086368856813079) 160000000000000000),
            (exactRationalLiteral (998688384442559) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (6841881109626922793) 614400000000000000000),
            (exactRationalLiteral (27290136252361161) 2560000000000000000),
            (exactRationalLiteral (-6165893208778111) 800000000000000000),
            (exactRationalLiteral (-1052052299280457) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-14193673719792204277) 1228800000000000000000),
            (exactRationalLiteral (-842989693011937169) 25600000000000000000),
            (exactRationalLiteral (26971847486127107) 1600000000000000000),
            (exactRationalLiteral (18288129042431239) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (37739387822821409527) 1228800000000000000000),
            (exactRationalLiteral (3294299946274711979) 25600000000000000000),
            (exactRationalLiteral (13335372068496463) 1600000000000000000),
            (exactRationalLiteral (-42886178452196317) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3205197740225840059) 122880000000000000000),
            (exactRationalLiteral (-2558209417394013181) 12800000000000000000),
            (exactRationalLiteral (-84266228922404209) 800000000000000000),
            (exactRationalLiteral (30293563664291083) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-102788692083722599837) 1228800000000000000000),
            (exactRationalLiteral (2686237266187802087) 25600000000000000000),
            (exactRationalLiteral (266670251078461979) 1600000000000000000),
            (exactRationalLiteral (-49309903790619329) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2053015265868416993) 61440000000000000000),
            (exactRationalLiteral (68525925669306193) 6400000000000000000),
            (exactRationalLiteral (-43330173416753267) 400000000000000000),
            (exactRationalLiteral (5313200889452249) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1002063710003235187) 245760000000000000000),
            (exactRationalLiteral (-91096700909385017) 5120000000000000000),
            (exactRationalLiteral (8281518264489547) 320000000000000000),
            (exactRationalLiteral (-752865296771777) 60000000000000000)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ),
            (0 : ℚ)
          ],
          ![
            (0 : ℚ),
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
          (0 : ℚ),
          (exactRationalLiteral (6775787670945993) 1280000000000000000),
          (exactRationalLiteral (648226201721168261) 19200000000000000000),
          (exactRationalLiteral (1718720050394687513) 19200000000000000000),
          (exactRationalLiteral (365898823482495877) 9600000000000000000),
          (exactRationalLiteral (1984141983308284939) 51200000000000000000),
          (exactRationalLiteral (692643296971966801) 51200000000000000000),
          (exactRationalLiteral (903697414611020563) 76800000000000000000),
          (exactRationalLiteral (1381582934940256121) 76800000000000000000),
          (exactRationalLiteral (88797560653148497) 3200000000000000000),
          (exactRationalLiteral (2302710111647836147) 51200000000000000000),
          (exactRationalLiteral (269794749742806551) 6144000000000000000),
          (exactRationalLiteral (3043581321209351) 1600000000000000000),
          (exactRationalLiteral (2018543047151303) 6400000000000000000),
          (exactRationalLiteral (14644593310009711) 2400000000000000000),
          (exactRationalLiteral (473360072661308717) 19200000000000000000),
          (exactRationalLiteral (983312617099567) 80000000000000000),
          (exactRationalLiteral (289046606468479801) 19200000000000000000),
          (exactRationalLiteral (28124211435319539) 6400000000000000000),
          (exactRationalLiteral (1425950770322860391) 19200000000000000000),
          (exactRationalLiteral (1483303149222543917) 9600000000000000000),
          (exactRationalLiteral (1425950770322860391) 19200000000000000000),
          (exactRationalLiteral (28124211435319539) 6400000000000000000),
          (exactRationalLiteral (289046606468479801) 19200000000000000000),
          (exactRationalLiteral (983312617099567) 80000000000000000),
          (exactRationalLiteral (473360072661308717) 19200000000000000000),
          (exactRationalLiteral (14644593310009711) 2400000000000000000),
          (exactRationalLiteral (2018543047151303) 6400000000000000000),
          (exactRationalLiteral (3043581321209351) 1600000000000000000),
          (exactRationalLiteral (269794749742806551) 6144000000000000000),
          (exactRationalLiteral (2302710111647836147) 51200000000000000000),
          (exactRationalLiteral (88797560653148497) 3200000000000000000),
          (exactRationalLiteral (1381582934940256121) 76800000000000000000),
          (exactRationalLiteral (903697414611020563) 76800000000000000000),
          (exactRationalLiteral (692643296971966801) 51200000000000000000),
          (exactRationalLiteral (1984141983308284939) 51200000000000000000),
          (exactRationalLiteral (365898823482495877) 9600000000000000000),
          (exactRationalLiteral (1718720050394687513) 19200000000000000000),
          (exactRationalLiteral (648226201721168261) 19200000000000000000),
          (exactRationalLiteral (6775787670945993) 1280000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (39, 6),
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
      (37, 1)
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
      true
    ]
  }
]

/-- All centered cubic, true Bernstein, center and radius checks are exact. -/
theorem generatorCoordinates33_valid : ∀ i, (generatorCoordinates33 i).IsValid := by
  have h : ∀ i, (generatorCoordinates33 i).FastIsValid := by
    unfold GeneratorCoordinateData.FastIsValid GeneratorCubicIntervalData.FastIsValid
    decide +kernel
  intro i
  exact GeneratorCoordinateData.isValid_of_fast (h i)

end PartialBalayage.Maximal.Square
