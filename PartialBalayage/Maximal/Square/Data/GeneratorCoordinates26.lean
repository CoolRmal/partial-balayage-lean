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

/-- Actual coordinate interval candidates, block 26. -/
def generatorCoordinates26 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 6
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
            (exactRationalLiteral (3710615129098238777) 614400000000000000000),
            (exactRationalLiteral (-285431933007556829) 12800000000000000000),
            (exactRationalLiteral (21956302539042833) 800000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (18635091076237856251) 614400000000000000000),
            (exactRationalLiteral (446688386667439521) 12800000000000000000),
            (exactRationalLiteral (-99193642748727629) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-35675412460383115553) 409600000000000000000),
            (exactRationalLiteral (1540885232906209023) 25600000000000000000),
            (exactRationalLiteral (342278885377181109) 1600000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1335017542625291987) 30720000000000000000),
            (exactRationalLiteral (-516282873506148111) 3200000000000000000),
            (exactRationalLiteral (-34019312927143601) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (6219610773496130867) 409600000000000000000),
            (exactRationalLiteral (2940986573184823443) 25600000000000000000),
            (exactRationalLiteral (89204345888244561) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-82084450490656637) 10240000000000000000),
            (exactRationalLiteral (-96972504251367057) 3200000000000000000),
            (exactRationalLiteral (-99777347127039) 40000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2224704323677549) 122880000000000000000),
            (exactRationalLiteral (76995099656521643) 12800000000000000000),
            (exactRationalLiteral (-153984506580967) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (295885547342244607) 1228800000000000000000),
            (exactRationalLiteral (-52143403074715579) 25600000000000000000),
            (exactRationalLiteral (-884929111352729) 1600000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4550982711415754989) 1228800000000000000000),
            (exactRationalLiteral (63333593532790671) 25600000000000000000),
            (exactRationalLiteral (1160504805486661) 1600000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (192025459898217229) 61440000000000000000),
            (exactRationalLiteral (388026573167439) 256000000000000000),
            (exactRationalLiteral (140886073608641) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-5660229438665661843) 409600000000000000000),
            (exactRationalLiteral (-84775819185475123) 25600000000000000000),
            (exactRationalLiteral (-1153472294105841) 1600000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-311113213512860233) 61440000000000000000),
            (exactRationalLiteral (-18897159938671163) 6400000000000000000),
            (exactRationalLiteral (-205415341650217) 80000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (2508171812768076601) 614400000000000000000),
            (exactRationalLiteral (63230432831952091) 12800000000000000000),
            (exactRationalLiteral (267334798296749) 160000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-641865359764254629) 307200000000000000000),
            (exactRationalLiteral (41405185173316881) 6400000000000000000),
            (exactRationalLiteral (-811196824181261) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-2145178663017690103) 245760000000000000000),
            (exactRationalLiteral (253738462984677551) 25600000000000000000),
            (exactRationalLiteral (-18823472386332731) 1600000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (18294583865739798077) 614400000000000000000),
            (exactRationalLiteral (-386418592484418897) 12800000000000000000),
            (exactRationalLiteral (19665317656462133) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (29533023306880095011) 307200000000000000000),
            (exactRationalLiteral (-102846287229752939) 1280000000000000000),
            (exactRationalLiteral (3143684063842687) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-19591878402773353227) 204800000000000000000),
            (exactRationalLiteral (1525277234618584637) 12800000000000000000),
            (exactRationalLiteral (-12711907840687701) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-29506000031488321567) 1228800000000000000000),
            (exactRationalLiteral (-333217166197951317) 25600000000000000000),
            (exactRationalLiteral (7844808230752837) 320000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-186114532216572431) 307200000000000000000),
            (exactRationalLiteral (-58035267469382293) 6400000000000000000),
            (exactRationalLiteral (2125456413598921) 400000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-131407932199860128807) 614400000000000000000),
            (exactRationalLiteral (1593120654609237339) 12800000000000000000),
            (exactRationalLiteral (-32511390905679167) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (278792096236475279383) 614400000000000000000),
            (exactRationalLiteral (-665890992331299031) 2560000000000000000),
            (exactRationalLiteral (65474263128265663) 800000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-131407932199860128807) 614400000000000000000),
            (exactRationalLiteral (1593120654609237339) 12800000000000000000),
            (exactRationalLiteral (-32511390905679167) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-186114532216572431) 307200000000000000000),
            (exactRationalLiteral (-58035267469382293) 6400000000000000000),
            (exactRationalLiteral (2125456413598921) 400000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-29506000031488321567) 1228800000000000000000),
            (exactRationalLiteral (-333217166197951317) 25600000000000000000),
            (exactRationalLiteral (7844808230752837) 320000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19591878402773353227) 204800000000000000000),
            (exactRationalLiteral (1525277234618584637) 12800000000000000000),
            (exactRationalLiteral (-12711907840687701) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (29533023306880095011) 307200000000000000000),
            (exactRationalLiteral (-102846287229752939) 1280000000000000000),
            (exactRationalLiteral (3143684063842687) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (18294583865739798077) 614400000000000000000),
            (exactRationalLiteral (-386418592484418897) 12800000000000000000),
            (exactRationalLiteral (19665317656462133) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2145178663017690103) 245760000000000000000),
            (exactRationalLiteral (253738462984677551) 25600000000000000000),
            (exactRationalLiteral (-18823472386332731) 1600000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-641865359764254629) 307200000000000000000),
            (exactRationalLiteral (41405185173316881) 6400000000000000000),
            (exactRationalLiteral (-811196824181261) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (2508171812768076601) 614400000000000000000),
            (exactRationalLiteral (63230432831952091) 12800000000000000000),
            (exactRationalLiteral (267334798296749) 160000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-311113213512860233) 61440000000000000000),
            (exactRationalLiteral (-18897159938671163) 6400000000000000000),
            (exactRationalLiteral (-205415341650217) 80000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-5660229438665661843) 409600000000000000000),
            (exactRationalLiteral (-84775819185475123) 25600000000000000000),
            (exactRationalLiteral (-1153472294105841) 1600000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (192025459898217229) 61440000000000000000),
            (exactRationalLiteral (388026573167439) 256000000000000000),
            (exactRationalLiteral (140886073608641) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (4550982711415754989) 1228800000000000000000),
            (exactRationalLiteral (63333593532790671) 25600000000000000000),
            (exactRationalLiteral (1160504805486661) 1600000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (295885547342244607) 1228800000000000000000),
            (exactRationalLiteral (-52143403074715579) 25600000000000000000),
            (exactRationalLiteral (-884929111352729) 1600000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2224704323677549) 122880000000000000000),
            (exactRationalLiteral (76995099656521643) 12800000000000000000),
            (exactRationalLiteral (-153984506580967) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-82084450490656637) 10240000000000000000),
            (exactRationalLiteral (-96972504251367057) 3200000000000000000),
            (exactRationalLiteral (-99777347127039) 40000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (6219610773496130867) 409600000000000000000),
            (exactRationalLiteral (2940986573184823443) 25600000000000000000),
            (exactRationalLiteral (89204345888244561) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1335017542625291987) 30720000000000000000),
            (exactRationalLiteral (-516282873506148111) 3200000000000000000),
            (exactRationalLiteral (-34019312927143601) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-35675412460383115553) 409600000000000000000),
            (exactRationalLiteral (1540885232906209023) 25600000000000000000),
            (exactRationalLiteral (342278885377181109) 1600000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (18635091076237856251) 614400000000000000000),
            (exactRationalLiteral (446688386667439521) 12800000000000000000),
            (exactRationalLiteral (-99193642748727629) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (3710615129098238777) 614400000000000000000),
            (exactRationalLiteral (-285431933007556829) 12800000000000000000),
            (exactRationalLiteral (21956302539042833) 800000000000000000),
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
          (exactRationalLiteral (579308597760899363) 76800000000000000000),
          (exactRationalLiteral (307616268887703667) 9600000000000000000),
          (exactRationalLiteral (13821840629366760841) 153600000000000000000),
          (exactRationalLiteral (1014299258150906707) 19200000000000000000),
          (exactRationalLiteral (432916670094305603) 19200000000000000000),
          (exactRationalLiteral (23773474834382461) 2400000000000000000),
          (exactRationalLiteral (748115110260623) 1920000000000000000),
          (exactRationalLiteral (56053341894242053) 153600000000000000000),
          (exactRationalLiteral (24708249992951501) 6400000000000000000),
          (exactRationalLiteral (161095837902993) 50000000000000000),
          (exactRationalLiteral (269358433629117907) 19200000000000000000),
          (exactRationalLiteral (1261984107402161) 240000000000000000),
          (exactRationalLiteral (1688828912734673) 384000000000000000),
          (exactRationalLiteral (96043171281862507) 38400000000000000000),
          (exactRationalLiteral (1443213000135336601) 153600000000000000000),
          (exactRationalLiteral (2439292150773224863) 76800000000000000000),
          (exactRationalLiteral (1296816602189339599) 12800000000000000000),
          (exactRationalLiteral (7943224972329715679) 76800000000000000000),
          (exactRationalLiteral (474858237907893221) 19200000000000000000),
          (exactRationalLiteral (5529853662083201) 4800000000000000000),
          (exactRationalLiteral (5678577940743842987) 25600000000000000000),
          (exactRationalLiteral (36122371043331111437) 76800000000000000000),
          (exactRationalLiteral (5678577940743842987) 25600000000000000000),
          (exactRationalLiteral (5529853662083201) 4800000000000000000),
          (exactRationalLiteral (474858237907893221) 19200000000000000000),
          (exactRationalLiteral (7943224972329715679) 76800000000000000000),
          (exactRationalLiteral (1296816602189339599) 12800000000000000000),
          (exactRationalLiteral (2439292150773224863) 76800000000000000000),
          (exactRationalLiteral (1443213000135336601) 153600000000000000000),
          (exactRationalLiteral (96043171281862507) 38400000000000000000),
          (exactRationalLiteral (1688828912734673) 384000000000000000),
          (exactRationalLiteral (1261984107402161) 240000000000000000),
          (exactRationalLiteral (269358433629117907) 19200000000000000000),
          (exactRationalLiteral (161095837902993) 50000000000000000),
          (exactRationalLiteral (24708249992951501) 6400000000000000000),
          (exactRationalLiteral (56053341894242053) 153600000000000000000),
          (exactRationalLiteral (748115110260623) 1920000000000000000),
          (exactRationalLiteral (23773474834382461) 2400000000000000000),
          (exactRationalLiteral (432916670094305603) 19200000000000000000),
          (exactRationalLiteral (1014299258150906707) 19200000000000000000),
          (exactRationalLiteral (13821840629366760841) 153600000000000000000),
          (exactRationalLiteral (307616268887703667) 9600000000000000000),
          (exactRationalLiteral (579308597760899363) 76800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 10),
      (37, 18)
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
            (exactRationalLiteral (2247987590728154671) 614400000000000000000),
            (exactRationalLiteral (-204362508248014061) 12800000000000000000),
            (exactRationalLiteral (18578409840728551) 800000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (20203824889810103917) 614400000000000000000),
            (exactRationalLiteral (89377418948700049) 12800000000000000000),
            (exactRationalLiteral (-79461841110642107) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-94052230469604668597) 1228800000000000000000),
            (exactRationalLiteral (2720675219205558767) 25600000000000000000),
            (exactRationalLiteral (247616107772493763) 1600000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3229033354213606529) 153600000000000000000),
            (exactRationalLiteral (-622422806589843279) 3200000000000000000),
            (exactRationalLiteral (-19050653614703983) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (37033298376879963823) 1228800000000000000000),
            (exactRationalLiteral (3126851190049649603) 25600000000000000000),
            (exactRationalLiteral (3727962544168519) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1801660096332643781) 153600000000000000000),
            (exactRationalLiteral (-90253887512392609) 3200000000000000000),
            (exactRationalLiteral (3858195105122419) 200000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (30216403413337513) 40960000000000000000),
            (exactRationalLiteral (67379034490956123) 12800000000000000000),
            (exactRationalLiteral (-4654048076201793) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-17720147815107751) 1228800000000000000000),
            (exactRationalLiteral (-50746183206539563) 25600000000000000000),
            (exactRationalLiteral (1583539045440737) 1600000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4941062268007148603) 1228800000000000000000),
            (exactRationalLiteral (66051581619142143) 25600000000000000000),
            (exactRationalLiteral (7939569507563) 64000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1020988937361657679) 307200000000000000000),
            (exactRationalLiteral (2149543625939307) 1280000000000000000),
            (exactRationalLiteral (382640826646639) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-140055147146093179) 9830400000000000000),
            (exactRationalLiteral (-18248791134633799) 5120000000000000000),
            (exactRationalLiteral (-416119189948219) 320000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-560426995817642177) 102400000000000000000),
            (exactRationalLiteral (-23008986650468187) 6400000000000000000),
            (exactRationalLiteral (-1028836647647427) 400000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (193707967650289041) 40960000000000000000),
            (exactRationalLiteral (13917927469251567) 2560000000000000000),
            (exactRationalLiteral (1842928265669127) 800000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-404521694629320467) 307200000000000000000),
            (exactRationalLiteral (37483855869195841) 6400000000000000000),
            (exactRationalLiteral (-1149467827879259) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1882469033353337281) 245760000000000000000),
            (exactRationalLiteral (37388818592838483) 5120000000000000000),
            (exactRationalLiteral (-14573712623909837) 1600000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (3240008648504793679) 122880000000000000000),
            (exactRationalLiteral (-313763761952001313) 12800000000000000000),
            (exactRationalLiteral (16662097609746659) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (8876817041245700087) 102400000000000000000),
            (exactRationalLiteral (-90852011982478971) 1280000000000000000),
            (exactRationalLiteral (2853453559794297) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-50357452280237043319) 614400000000000000000),
            (exactRationalLiteral (1285656073211215917) 12800000000000000000),
            (exactRationalLiteral (-11250208300049171) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-10352732363568374899) 409600000000000000000),
            (exactRationalLiteral (-188112279520027301) 25600000000000000000),
            (exactRationalLiteral (33328402185197823) 1600000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-509354011984897673) 307200000000000000000),
            (exactRationalLiteral (-49800117772595877) 6400000000000000000),
            (exactRationalLiteral (1992118434794287) 400000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-40743669010498009291) 204800000000000000000),
            (exactRationalLiteral (1467244056775934123) 12800000000000000000),
            (exactRationalLiteral (-30426908010972441) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (259584382137520859137) 614400000000000000000),
            (exactRationalLiteral (-3075895652420751139) 12800000000000000000),
            (exactRationalLiteral (12261078297921269) 160000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-40743669010498009291) 204800000000000000000),
            (exactRationalLiteral (1467244056775934123) 12800000000000000000),
            (exactRationalLiteral (-30426908010972441) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-509354011984897673) 307200000000000000000),
            (exactRationalLiteral (-49800117772595877) 6400000000000000000),
            (exactRationalLiteral (1992118434794287) 400000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-10352732363568374899) 409600000000000000000),
            (exactRationalLiteral (-188112279520027301) 25600000000000000000),
            (exactRationalLiteral (33328402185197823) 1600000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-50357452280237043319) 614400000000000000000),
            (exactRationalLiteral (1285656073211215917) 12800000000000000000),
            (exactRationalLiteral (-11250208300049171) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (8876817041245700087) 102400000000000000000),
            (exactRationalLiteral (-90852011982478971) 1280000000000000000),
            (exactRationalLiteral (2853453559794297) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (3240008648504793679) 122880000000000000000),
            (exactRationalLiteral (-313763761952001313) 12800000000000000000),
            (exactRationalLiteral (16662097609746659) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1882469033353337281) 245760000000000000000),
            (exactRationalLiteral (37388818592838483) 5120000000000000000),
            (exactRationalLiteral (-14573712623909837) 1600000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-404521694629320467) 307200000000000000000),
            (exactRationalLiteral (37483855869195841) 6400000000000000000),
            (exactRationalLiteral (-1149467827879259) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (193707967650289041) 40960000000000000000),
            (exactRationalLiteral (13917927469251567) 2560000000000000000),
            (exactRationalLiteral (1842928265669127) 800000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-560426995817642177) 102400000000000000000),
            (exactRationalLiteral (-23008986650468187) 6400000000000000000),
            (exactRationalLiteral (-1028836647647427) 400000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-140055147146093179) 9830400000000000000),
            (exactRationalLiteral (-18248791134633799) 5120000000000000000),
            (exactRationalLiteral (-416119189948219) 320000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1020988937361657679) 307200000000000000000),
            (exactRationalLiteral (2149543625939307) 1280000000000000000),
            (exactRationalLiteral (382640826646639) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (4941062268007148603) 1228800000000000000000),
            (exactRationalLiteral (66051581619142143) 25600000000000000000),
            (exactRationalLiteral (7939569507563) 64000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-17720147815107751) 1228800000000000000000),
            (exactRationalLiteral (-50746183206539563) 25600000000000000000),
            (exactRationalLiteral (1583539045440737) 1600000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (30216403413337513) 40960000000000000000),
            (exactRationalLiteral (67379034490956123) 12800000000000000000),
            (exactRationalLiteral (-4654048076201793) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1801660096332643781) 153600000000000000000),
            (exactRationalLiteral (-90253887512392609) 3200000000000000000),
            (exactRationalLiteral (3858195105122419) 200000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (37033298376879963823) 1228800000000000000000),
            (exactRationalLiteral (3126851190049649603) 25600000000000000000),
            (exactRationalLiteral (3727962544168519) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3229033354213606529) 153600000000000000000),
            (exactRationalLiteral (-622422806589843279) 3200000000000000000),
            (exactRationalLiteral (-19050653614703983) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-94052230469604668597) 1228800000000000000000),
            (exactRationalLiteral (2720675219205558767) 25600000000000000000),
            (exactRationalLiteral (247616107772493763) 1600000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (20203824889810103917) 614400000000000000000),
            (exactRationalLiteral (89377418948700049) 12800000000000000000),
            (exactRationalLiteral (-79461841110642107) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2247987590728154671) 614400000000000000000),
            (exactRationalLiteral (-204362508248014061) 12800000000000000000),
            (exactRationalLiteral (18578409840728551) 800000000000000000),
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
          (exactRationalLiteral (1272674890565650207) 38400000000000000000),
          (exactRationalLiteral (1584751193985961249) 19200000000000000000),
          (exactRationalLiteral (13103295529903137) 400000000000000000),
          (exactRationalLiteral (1932595735124557507) 51200000000000000000),
          (exactRationalLiteral (85777859693086481) 6400000000000000000),
          (exactRationalLiteral (79896372332439409) 76800000000000000000),
          (exactRationalLiteral (20496730777500937) 153600000000000000000),
          (exactRationalLiteral (642416434099217933) 153600000000000000000),
          (exactRationalLiteral (5272504458036031) 1536000000000000000),
          (exactRationalLiteral (741138775414924803) 51200000000000000000),
          (exactRationalLiteral (219174417164621443) 38400000000000000000),
          (exactRationalLiteral (390021292340901149) 76800000000000000000),
          (exactRationalLiteral (8128945784667137) 4800000000000000000),
          (exactRationalLiteral (156547241615815697) 19200000000000000000),
          (exactRationalLiteral (268637850488008907) 9600000000000000000),
          (exactRationalLiteral (438074354423926879) 4800000000000000000),
          (exactRationalLiteral (169958837103821953) 1920000000000000000),
          (exactRationalLiteral (3940687067774237039) 153600000000000000000),
          (exactRationalLiteral (16321116974692619) 7680000000000000000),
          (exactRationalLiteral (1980079096364095327) 9600000000000000000),
          (exactRationalLiteral (4203094839141738457) 9600000000000000000),
          (exactRationalLiteral (1980079096364095327) 9600000000000000000),
          (exactRationalLiteral (16321116974692619) 7680000000000000000),
          (exactRationalLiteral (3940687067774237039) 153600000000000000000),
          (exactRationalLiteral (169958837103821953) 1920000000000000000),
          (exactRationalLiteral (438074354423926879) 4800000000000000000),
          (exactRationalLiteral (268637850488008907) 9600000000000000000),
          (exactRationalLiteral (156547241615815697) 19200000000000000000),
          (exactRationalLiteral (8128945784667137) 4800000000000000000),
          (exactRationalLiteral (390021292340901149) 76800000000000000000),
          (exactRationalLiteral (219174417164621443) 38400000000000000000),
          (exactRationalLiteral (741138775414924803) 51200000000000000000),
          (exactRationalLiteral (5272504458036031) 1536000000000000000),
          (exactRationalLiteral (642416434099217933) 153600000000000000000),
          (exactRationalLiteral (20496730777500937) 153600000000000000000),
          (exactRationalLiteral (79896372332439409) 76800000000000000000),
          (exactRationalLiteral (85777859693086481) 6400000000000000000),
          (exactRationalLiteral (1932595735124557507) 51200000000000000000),
          (exactRationalLiteral (13103295529903137) 400000000000000000),
          (exactRationalLiteral (1584751193985961249) 19200000000000000000),
          (exactRationalLiteral (1272674890565650207) 38400000000000000000),
          (exactRationalLiteral (15200517142414269) 3200000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 9),
      (37, 17)
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
            (exactRationalLiteral (410413962845185263) 204800000000000000000),
            (exactRationalLiteral (-136804654281728421) 12800000000000000000),
            (exactRationalLiteral (15200517142414269) 800000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3973094903345388203) 122880000000000000000),
            (exactRationalLiteral (-37801268443539467) 2560000000000000000),
            (exactRationalLiteral (-11946007894511317) 160000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-75135436971520140223) 1228800000000000000000),
            (exactRationalLiteral (3521814095086159127) 25600000000000000000),
            (exactRationalLiteral (152953330167806417) 1600000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-224745563817380823) 51200000000000000000),
            (exactRationalLiteral (-26747524096951199) 128000000000000000),
            (exactRationalLiteral (-816398860452873) 40000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (55497235534331579501) 1228800000000000000000),
            (exactRationalLiteral (594162054707634319) 5120000000000000000),
            (exactRationalLiteral (-81748420799907523) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2279456752782499951) 153600000000000000000),
            (exactRationalLiteral (-13221388682077541) 640000000000000000),
            (exactRationalLiteral (8215276945880033) 200000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (783671426952894613) 614400000000000000000),
            (exactRationalLiteral (39762715046907299) 12800000000000000000),
            (exactRationalLiteral (-9154111645822619) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-97773635293960807) 409600000000000000000),
            (exactRationalLiteral (-39475090711189683) 25600000000000000000),
            (exactRationalLiteral (4052007202234203) 1600000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1778635188767693339) 409600000000000000000),
            (exactRationalLiteral (64921507434303271) 25600000000000000000),
            (exactRationalLiteral (-763526330108511) 1600000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (363677985023916183) 102400000000000000000),
            (exactRationalLiteral (12761790942359087) 6400000000000000000),
            (exactRationalLiteral (624395579684637) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-18083032773320095501) 1228800000000000000000),
            (exactRationalLiteral (-101420586783403883) 25600000000000000000),
            (exactRationalLiteral (-3007719605376349) 1600000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-366337597377018029) 61440000000000000000),
            (exactRationalLiteral (-27127853119850579) 6400000000000000000),
            (exactRationalLiteral (-1030596587043769) 400000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (3347297495116653677) 614400000000000000000),
            (exactRationalLiteral (77973858957305107) 12800000000000000000),
            (exactRationalLiteral (2349182539854509) 800000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-194765257363488521) 307200000000000000000),
            (exactRationalLiteral (32209442550282809) 6400000000000000000),
            (exactRationalLiteral (-1487738831577257) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-8448566121418758383) 1228800000000000000000),
            (exactRationalLiteral (27429752398679771) 5120000000000000000),
            (exactRationalLiteral (-10323952861486943) 1600000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (14505392961942058529) 614400000000000000000),
            (exactRationalLiteral (-404994898570313) 20480000000000000),
            (exactRationalLiteral (2731775512606237) 160000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (24070293367769421151) 307200000000000000000),
            (exactRationalLiteral (-80018658751398563) 1280000000000000000),
            (exactRationalLiteral (2563223055745907) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-43289294348159927477) 614400000000000000000),
            (exactRationalLiteral (1075268902616617797) 12800000000000000000),
            (exactRationalLiteral (-9788508759410641) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-1272420499899087203) 49152000000000000000),
            (exactRationalLiteral (-66589948716368733) 25600000000000000000),
            (exactRationalLiteral (27432763216631461) 1600000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-784782649318160027) 307200000000000000000),
            (exactRationalLiteral (-42098319991027997) 6400000000000000000),
            (exactRationalLiteral (1858780455989653) 400000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-113784327655391265523) 614400000000000000000),
            (exactRationalLiteral (1349705390521457811) 12800000000000000000),
            (exactRationalLiteral (-5668485023253143) 160000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (241847997434316991171) 614400000000000000000),
            (exactRationalLiteral (-567802365947928879) 2560000000000000000),
            (exactRationalLiteral (57136519850947027) 800000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-113784327655391265523) 614400000000000000000),
            (exactRationalLiteral (1349705390521457811) 12800000000000000000),
            (exactRationalLiteral (-5668485023253143) 160000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-784782649318160027) 307200000000000000000),
            (exactRationalLiteral (-42098319991027997) 6400000000000000000),
            (exactRationalLiteral (1858780455989653) 400000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1272420499899087203) 49152000000000000000),
            (exactRationalLiteral (-66589948716368733) 25600000000000000000),
            (exactRationalLiteral (27432763216631461) 1600000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-43289294348159927477) 614400000000000000000),
            (exactRationalLiteral (1075268902616617797) 12800000000000000000),
            (exactRationalLiteral (-9788508759410641) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (24070293367769421151) 307200000000000000000),
            (exactRationalLiteral (-80018658751398563) 1280000000000000000),
            (exactRationalLiteral (2563223055745907) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (14505392961942058529) 614400000000000000000),
            (exactRationalLiteral (-404994898570313) 20480000000000000),
            (exactRationalLiteral (2731775512606237) 160000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-8448566121418758383) 1228800000000000000000),
            (exactRationalLiteral (27429752398679771) 5120000000000000000),
            (exactRationalLiteral (-10323952861486943) 1600000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-194765257363488521) 307200000000000000000),
            (exactRationalLiteral (32209442550282809) 6400000000000000000),
            (exactRationalLiteral (-1487738831577257) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (3347297495116653677) 614400000000000000000),
            (exactRationalLiteral (77973858957305107) 12800000000000000000),
            (exactRationalLiteral (2349182539854509) 800000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-366337597377018029) 61440000000000000000),
            (exactRationalLiteral (-27127853119850579) 6400000000000000000),
            (exactRationalLiteral (-1030596587043769) 400000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-18083032773320095501) 1228800000000000000000),
            (exactRationalLiteral (-101420586783403883) 25600000000000000000),
            (exactRationalLiteral (-3007719605376349) 1600000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (363677985023916183) 102400000000000000000),
            (exactRationalLiteral (12761790942359087) 6400000000000000000),
            (exactRationalLiteral (624395579684637) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1778635188767693339) 409600000000000000000),
            (exactRationalLiteral (64921507434303271) 25600000000000000000),
            (exactRationalLiteral (-763526330108511) 1600000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-97773635293960807) 409600000000000000000),
            (exactRationalLiteral (-39475090711189683) 25600000000000000000),
            (exactRationalLiteral (4052007202234203) 1600000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (783671426952894613) 614400000000000000000),
            (exactRationalLiteral (39762715046907299) 12800000000000000000),
            (exactRationalLiteral (-9154111645822619) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2279456752782499951) 153600000000000000000),
            (exactRationalLiteral (-13221388682077541) 640000000000000000),
            (exactRationalLiteral (8215276945880033) 200000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (55497235534331579501) 1228800000000000000000),
            (exactRationalLiteral (594162054707634319) 5120000000000000000),
            (exactRationalLiteral (-81748420799907523) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-224745563817380823) 51200000000000000000),
            (exactRationalLiteral (-26747524096951199) 128000000000000000),
            (exactRationalLiteral (-816398860452873) 40000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-75135436971520140223) 1228800000000000000000),
            (exactRationalLiteral (3521814095086159127) 25600000000000000000),
            (exactRationalLiteral (152953330167806417) 1600000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3973094903345388203) 122880000000000000000),
            (exactRationalLiteral (-37801268443539467) 2560000000000000000),
            (exactRationalLiteral (-11946007894511317) 160000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (410413962845185263) 204800000000000000000),
            (exactRationalLiteral (-136804654281728421) 12800000000000000000),
            (exactRationalLiteral (15200517142414269) 800000000000000000),
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
          (exactRationalLiteral (1688946349157141) 614400000000000000),
          (exactRationalLiteral (2530429690517915063) 76800000000000000000),
          (exactRationalLiteral (709955732312273789) 10240000000000000000),
          (exactRationalLiteral (2097705196854731) 120000000000000000),
          (exactRationalLiteral (125237661915770183) 2400000000000000000),
          (exactRationalLiteral (59837724884171) 3750000000000000),
          (exactRationalLiteral (113704063199393) 80000000000000000),
          (exactRationalLiteral (778038910801469) 2400000000000000000),
          (exactRationalLiteral (10796676761390167) 2400000000000000000),
          (exactRationalLiteral (883838587511249) 240000000000000000),
          (exactRationalLiteral (35931213387332527) 2400000000000000000),
          (exactRationalLiteral (499001097910279) 80000000000000000),
          (exactRationalLiteral (292034484598407) 50000000000000000),
          (exactRationalLiteral (7392191650180493) 7680000000000000000),
          (exactRationalLiteral (1111638643233078403) 153600000000000000000),
          (exactRationalLiteral (1913404579934230837) 76800000000000000000),
          (exactRationalLiteral (3163718396392088647) 38400000000000000000),
          (exactRationalLiteral (1944399289010522367) 25600000000000000000),
          (exactRationalLiteral (20788367105117627) 800000000000000000),
          (exactRationalLiteral (1768687376782573) 600000000000000000),
          (exactRationalLiteral (14739939167968973683) 76800000000000000000),
          (exactRationalLiteral (31317315864863511887) 76800000000000000000),
          (exactRationalLiteral (14739939167968973683) 76800000000000000000),
          (exactRationalLiteral (1768687376782573) 600000000000000000),
          (exactRationalLiteral (20788367105117627) 800000000000000000),
          (exactRationalLiteral (1944399289010522367) 25600000000000000000),
          (exactRationalLiteral (3163718396392088647) 38400000000000000000),
          (exactRationalLiteral (1913404579934230837) 76800000000000000000),
          (exactRationalLiteral (1111638643233078403) 153600000000000000000),
          (exactRationalLiteral (7392191650180493) 7680000000000000000),
          (exactRationalLiteral (292034484598407) 50000000000000000),
          (exactRationalLiteral (499001097910279) 80000000000000000),
          (exactRationalLiteral (35931213387332527) 2400000000000000000),
          (exactRationalLiteral (883838587511249) 240000000000000000),
          (exactRationalLiteral (10796676761390167) 2400000000000000000),
          (exactRationalLiteral (778038910801469) 2400000000000000000),
          (exactRationalLiteral (113704063199393) 80000000000000000),
          (exactRationalLiteral (59837724884171) 3750000000000000),
          (exactRationalLiteral (125237661915770183) 2400000000000000000),
          (exactRationalLiteral (2097705196854731) 120000000000000000),
          (exactRationalLiteral (709955732312273789) 10240000000000000000),
          (exactRationalLiteral (2530429690517915063) 76800000000000000000),
          (exactRationalLiteral (1688946349157141) 614400000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 8),
      (37, 16)
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
            (exactRationalLiteral (579308597760899363) 614400000000000000000),
            (exactRationalLiteral (-82758371108699909) 12800000000000000000),
            (exactRationalLiteral (11822624444099987) 800000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (18093603196302420073) 614400000000000000000),
            (exactRationalLiteral (-388462896831752631) 12800000000000000000),
            (exactRationalLiteral (-39998237834471063) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-17515921183136085947) 409600000000000000000),
            (exactRationalLiteral (3944301860548010103) 25600000000000000000),
            (exactRationalLiteral (58290552563119071) 1600000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4675474600372236227) 153600000000000000000),
            (exactRationalLiteral (-655078761007958199) 3200000000000000000),
            (exactRationalLiteral (10886665010175253) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (23999736864195138209) 409600000000000000000),
            (exactRationalLiteral (2472863823650389419) 25600000000000000000),
            (exactRationalLiteral (-33444960828796713) 320000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-853362254177078443) 51200000000000000000),
            (exactRationalLiteral (-4906334389070469) 640000000000000000),
            (exactRationalLiteral (12572358786637647) 200000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (35775924928239347) 24576000000000000000),
            (exactRationalLiteral (-5853858675624829) 12800000000000000000),
            (exactRationalLiteral (-2730835043088689) 160000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-471673491095036219) 1228800000000000000000),
            (exactRationalLiteral (-18330125588665939) 25600000000000000000),
            (exactRationalLiteral (6520475359027669) 1600000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5712424232676407167) 1228800000000000000000),
            (exactRationalLiteral (11988674195654811) 5120000000000000000),
            (exactRationalLiteral (-1725541897906097) 1600000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1176064466694270707) 307200000000000000000),
            (exactRationalLiteral (15742882767173631) 6400000000000000000),
            (exactRationalLiteral (173230066544527) 80000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-6243785807969192001) 409600000000000000000),
            (exactRationalLiteral (-115305712516179787) 25600000000000000000),
            (exactRationalLiteral (-3934843261011603) 1600000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-401365860881260843) 61440000000000000000),
            (exactRationalLiteral (-31253759346818339) 6400000000000000000),
            (exactRationalLiteral (-1032356526440111) 400000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (769071171287095991) 122880000000000000000),
            (exactRationalLiteral (88383097665093907) 12800000000000000000),
            (exactRationalLiteral (2855436814039891) 800000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20714552055510743) 307200000000000000000),
            (exactRationalLiteral (5116389043315557) 1280000000000000000),
            (exactRationalLiteral (-365201967055051) 80000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-7732561944746516993) 1228800000000000000000),
            (exactRationalLiteral (104352470072296871) 25600000000000000000),
            (exactRationalLiteral (-6074193099064049) 1600000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (13138555742872897103) 614400000000000000000),
            (exactRationalLiteral (-204492741447751833) 12800000000000000000),
            (exactRationalLiteral (10655657516315711) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (21817722378491250881) 307200000000000000000),
            (exactRationalLiteral (-14069245507302343) 256000000000000000),
            (exactRationalLiteral (2272992551697517) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-2493050497814139237) 40960000000000000000),
            (exactRationalLiteral (894115722834790277) 12800000000000000000),
            (exactRationalLiteral (-8326809218772111) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-31904441587050080389) 1228800000000000000000),
            (exactRationalLiteral (31349826213024387) 25600000000000000000),
            (exactRationalLiteral (21537124248065099) 1600000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1015600555707670709) 307200000000000000000),
            (exactRationalLiteral (-34929874124678653) 6400000000000000000),
            (exactRationalLiteral (1725442477185019) 400000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-106017866482078880333) 614400000000000000000),
            (exactRationalLiteral (1240504655845808403) 12800000000000000000),
            (exactRationalLiteral (-26257942221558989) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (225482889207535851853) 614400000000000000000),
            (exactRationalLiteral (-2618803493613174923) 12800000000000000000),
            (exactRationalLiteral (52967648212287709) 800000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-106017866482078880333) 614400000000000000000),
            (exactRationalLiteral (1240504655845808403) 12800000000000000000),
            (exactRationalLiteral (-26257942221558989) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1015600555707670709) 307200000000000000000),
            (exactRationalLiteral (-34929874124678653) 6400000000000000000),
            (exactRationalLiteral (1725442477185019) 400000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-31904441587050080389) 1228800000000000000000),
            (exactRationalLiteral (31349826213024387) 25600000000000000000),
            (exactRationalLiteral (21537124248065099) 1600000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2493050497814139237) 40960000000000000000),
            (exactRationalLiteral (894115722834790277) 12800000000000000000),
            (exactRationalLiteral (-8326809218772111) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (21817722378491250881) 307200000000000000000),
            (exactRationalLiteral (-14069245507302343) 256000000000000000),
            (exactRationalLiteral (2272992551697517) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (13138555742872897103) 614400000000000000000),
            (exactRationalLiteral (-204492741447751833) 12800000000000000000),
            (exactRationalLiteral (10655657516315711) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-7732561944746516993) 1228800000000000000000),
            (exactRationalLiteral (104352470072296871) 25600000000000000000),
            (exactRationalLiteral (-6074193099064049) 1600000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-20714552055510743) 307200000000000000000),
            (exactRationalLiteral (5116389043315557) 1280000000000000000),
            (exactRationalLiteral (-365201967055051) 80000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (769071171287095991) 122880000000000000000),
            (exactRationalLiteral (88383097665093907) 12800000000000000000),
            (exactRationalLiteral (2855436814039891) 800000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-401365860881260843) 61440000000000000000),
            (exactRationalLiteral (-31253759346818339) 6400000000000000000),
            (exactRationalLiteral (-1032356526440111) 400000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-6243785807969192001) 409600000000000000000),
            (exactRationalLiteral (-115305712516179787) 25600000000000000000),
            (exactRationalLiteral (-3934843261011603) 1600000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1176064466694270707) 307200000000000000000),
            (exactRationalLiteral (15742882767173631) 6400000000000000000),
            (exactRationalLiteral (173230066544527) 80000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (5712424232676407167) 1228800000000000000000),
            (exactRationalLiteral (11988674195654811) 5120000000000000000),
            (exactRationalLiteral (-1725541897906097) 1600000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-471673491095036219) 1228800000000000000000),
            (exactRationalLiteral (-18330125588665939) 25600000000000000000),
            (exactRationalLiteral (6520475359027669) 1600000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (35775924928239347) 24576000000000000000),
            (exactRationalLiteral (-5853858675624829) 12800000000000000000),
            (exactRationalLiteral (-2730835043088689) 160000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-853362254177078443) 51200000000000000000),
            (exactRationalLiteral (-4906334389070469) 640000000000000000),
            (exactRationalLiteral (12572358786637647) 200000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (23999736864195138209) 409600000000000000000),
            (exactRationalLiteral (2472863823650389419) 25600000000000000000),
            (exactRationalLiteral (-33444960828796713) 320000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4675474600372236227) 153600000000000000000),
            (exactRationalLiteral (-655078761007958199) 3200000000000000000),
            (exactRationalLiteral (10886665010175253) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-17515921183136085947) 409600000000000000000),
            (exactRationalLiteral (3944301860548010103) 25600000000000000000),
            (exactRationalLiteral (58290552563119071) 1600000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (18093603196302420073) 614400000000000000000),
            (exactRationalLiteral (-388462896831752631) 12800000000000000000),
            (exactRationalLiteral (-39998237834471063) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (579308597760899363) 614400000000000000000),
            (exactRationalLiteral (-82758371108699909) 12800000000000000000),
            (exactRationalLiteral (11822624444099987) 800000000000000000),
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
          (exactRationalLiteral (275023606612890219) 6400000000000000000),
          (exactRationalLiteral (9859173682429074271) 153600000000000000000),
          (exactRationalLiteral (81230291693237629) 4800000000000000000),
          (exactRationalLiteral (2374104493000629) 1600000000000000000),
          (exactRationalLiteral (21077841987731429) 51200000000000000000),
          (exactRationalLiteral (245274863005567177) 51200000000000000000),
          (exactRationalLiteral (51083851807103271) 12800000000000000000),
          (exactRationalLiteral (95447713265334839) 6144000000000000000),
          (exactRationalLiteral (262961066499472217) 38400000000000000000),
          (exactRationalLiteral (102983114675249351) 15360000000000000000),
          (exactRationalLiteral (100360626669161) 300000000000000000),
          (exactRationalLiteral (630153657354829) 96000000000000000),
          (exactRationalLiteral (26924809667555581) 1200000000000000000),
          (exactRationalLiteral (1864236348964397) 25000000000000000),
          (exactRationalLiteral (39264317405126599) 600000000000000000),
          (exactRationalLiteral (249689659039026977) 9600000000000000000),
          (exactRationalLiteral (139410064954944241) 38400000000000000000),
          (exactRationalLiteral (17874218183224013) 100000000000000000),
          (exactRationalLiteral (456055248181311659) 1200000000000000000),
          (exactRationalLiteral (17874218183224013) 100000000000000000),
          (exactRationalLiteral (139410064954944241) 38400000000000000000),
          (exactRationalLiteral (249689659039026977) 9600000000000000000),
          (exactRationalLiteral (39264317405126599) 600000000000000000),
          (exactRationalLiteral (1864236348964397) 25000000000000000),
          (exactRationalLiteral (26924809667555581) 1200000000000000000),
          (exactRationalLiteral (630153657354829) 96000000000000000),
          (exactRationalLiteral (100360626669161) 300000000000000000),
          (exactRationalLiteral (102983114675249351) 15360000000000000000),
          (exactRationalLiteral (262961066499472217) 38400000000000000000),
          (exactRationalLiteral (95447713265334839) 6144000000000000000),
          (exactRationalLiteral (51083851807103271) 12800000000000000000),
          (exactRationalLiteral (245274863005567177) 51200000000000000000),
          (exactRationalLiteral (21077841987731429) 51200000000000000000),
          (exactRationalLiteral (2374104493000629) 1600000000000000000),
          (exactRationalLiteral (81230291693237629) 4800000000000000000),
          (exactRationalLiteral (9859173682429074271) 153600000000000000000),
          (exactRationalLiteral (275023606612890219) 6400000000000000000),
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
      (37, 7),
      (37, 15)
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
            (exactRationalLiteral (1688946349157141) 4915200000000000000),
            (exactRationalLiteral (-1688946349157141) 512000000000000000),
            (exactRationalLiteral (1688946349157141) 160000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (15361774167850593619) 614400000000000000000),
            (exactRationalLiteral (-508992244893465839) 12800000000000000000),
            (exactRationalLiteral (-20266436196385541) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-5712223373156303551) 245760000000000000000),
            (exactRationalLiteral (797627703118222339) 5120000000000000000),
            (exactRationalLiteral (-1454889001662731) 64000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8415432549048123913) 153600000000000000000),
            (exactRationalLiteral (-581594782342377951) 3200000000000000000),
            (exactRationalLiteral (25855324322614871) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (84487790351383644193) 1228800000000000000000),
            (exactRationalLiteral (65320473615452123) 1024000000000000000),
            (exactRationalLiteral (-252701187488059607) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2538980161400667179) 153600000000000000000),
            (exactRationalLiteral (34471926882713471) 3200000000000000000),
            (exactRationalLiteral (16929440627395261) 200000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (225808204762810019) 204800000000000000000),
            (exactRationalLiteral (-69470686676640261) 12800000000000000000),
            (exactRationalLiteral (-18154238785064271) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-493534667691525961) 1228800000000000000000),
            (exactRationalLiteral (12688712161031669) 25600000000000000000),
            (exactRationalLiteral (1797788703164227) 320000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6047529893499987989) 1228800000000000000000),
            (exactRationalLiteral (10223434450210899) 5120000000000000000),
            (exactRationalLiteral (-2687557465703683) 1600000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (256376517260427221) 61440000000000000000),
            (exactRationalLiteral (19690993604140167) 6400000000000000000),
            (exactRationalLiteral (1107905085760633) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-19474118312759334977) 1228800000000000000000),
            (exactRationalLiteral (-132899332871496707) 25600000000000000000),
            (exactRationalLiteral (-4861966916646857) 1600000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-735582392854026983) 102400000000000000000),
            (exactRationalLiteral (-35386705331371467) 6400000000000000000),
            (exactRationalLiteral (-1034116465836453) 400000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1470648233763754539) 204800000000000000000),
            (exactRationalLiteral (20163470693924847) 2560000000000000000),
            (exactRationalLiteral (3361691088225273) 800000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (21902383441172183) 61440000000000000000),
            (exactRationalLiteral (17601363868080769) 6400000000000000000),
            (exactRationalLiteral (-2164280838973253) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-7162338402451812779) 1228800000000000000000),
            (exactRationalLiteral (88555217200886463) 25600000000000000000),
            (exactRationalLiteral (-364886667328231) 320000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (12027454304195312741) 614400000000000000000),
            (exactRationalLiteral (-167876551475919937) 12800000000000000000),
            (exactRationalLiteral (7652437469600237) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (6612636831805594217) 102400000000000000000),
            (exactRationalLiteral (-61834718337818427) 1280000000000000000),
            (exactRationalLiteral (1982762047649127) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-32501437692516902953) 614400000000000000000),
            (exactRationalLiteral (742196533865733357) 12800000000000000000),
            (exactRationalLiteral (-6865109678133581) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-10493826564889806109) 409600000000000000000),
            (exactRationalLiteral (105707045268152059) 25600000000000000000),
            (exactRationalLiteral (15641485279498737) 1600000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-241001568528948187) 61440000000000000000),
            (exactRationalLiteral (-5658956034709569) 1280000000000000000),
            (exactRationalLiteral (318420899676077) 80000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-32960531974027970293) 204800000000000000000),
            (exactRationalLiteral (1139641852748985899) 12800000000000000000),
            (exactRationalLiteral (-24173459326852263) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (210389004537849617551) 614400000000000000000),
            (exactRationalLiteral (-2415270644041342723) 12800000000000000000),
            (exactRationalLiteral (48798776573628391) 800000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-32960531974027970293) 204800000000000000000),
            (exactRationalLiteral (1139641852748985899) 12800000000000000000),
            (exactRationalLiteral (-24173459326852263) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-241001568528948187) 61440000000000000000),
            (exactRationalLiteral (-5658956034709569) 1280000000000000000),
            (exactRationalLiteral (318420899676077) 80000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-10493826564889806109) 409600000000000000000),
            (exactRationalLiteral (105707045268152059) 25600000000000000000),
            (exactRationalLiteral (15641485279498737) 1600000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-32501437692516902953) 614400000000000000000),
            (exactRationalLiteral (742196533865733357) 12800000000000000000),
            (exactRationalLiteral (-6865109678133581) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (6612636831805594217) 102400000000000000000),
            (exactRationalLiteral (-61834718337818427) 1280000000000000000),
            (exactRationalLiteral (1982762047649127) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (12027454304195312741) 614400000000000000000),
            (exactRationalLiteral (-167876551475919937) 12800000000000000000),
            (exactRationalLiteral (7652437469600237) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-7162338402451812779) 1228800000000000000000),
            (exactRationalLiteral (88555217200886463) 25600000000000000000),
            (exactRationalLiteral (-364886667328231) 320000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (21902383441172183) 61440000000000000000),
            (exactRationalLiteral (17601363868080769) 6400000000000000000),
            (exactRationalLiteral (-2164280838973253) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (1470648233763754539) 204800000000000000000),
            (exactRationalLiteral (20163470693924847) 2560000000000000000),
            (exactRationalLiteral (3361691088225273) 800000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-735582392854026983) 102400000000000000000),
            (exactRationalLiteral (-35386705331371467) 6400000000000000000),
            (exactRationalLiteral (-1034116465836453) 400000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-19474118312759334977) 1228800000000000000000),
            (exactRationalLiteral (-132899332871496707) 25600000000000000000),
            (exactRationalLiteral (-4861966916646857) 1600000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (256376517260427221) 61440000000000000000),
            (exactRationalLiteral (19690993604140167) 6400000000000000000),
            (exactRationalLiteral (1107905085760633) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (6047529893499987989) 1228800000000000000000),
            (exactRationalLiteral (10223434450210899) 5120000000000000000),
            (exactRationalLiteral (-2687557465703683) 1600000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-493534667691525961) 1228800000000000000000),
            (exactRationalLiteral (12688712161031669) 25600000000000000000),
            (exactRationalLiteral (1797788703164227) 320000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (225808204762810019) 204800000000000000000),
            (exactRationalLiteral (-69470686676640261) 12800000000000000000),
            (exactRationalLiteral (-18154238785064271) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2538980161400667179) 153600000000000000000),
            (exactRationalLiteral (34471926882713471) 3200000000000000000),
            (exactRationalLiteral (16929440627395261) 200000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (84487790351383644193) 1228800000000000000000),
            (exactRationalLiteral (65320473615452123) 1024000000000000000),
            (exactRationalLiteral (-252701187488059607) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8415432549048123913) 153600000000000000000),
            (exactRationalLiteral (-581594782342377951) 3200000000000000000),
            (exactRationalLiteral (25855324322614871) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-5712223373156303551) 245760000000000000000),
            (exactRationalLiteral (797627703118222339) 5120000000000000000),
            (exactRationalLiteral (-1454889001662731) 64000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (15361774167850593619) 614400000000000000000),
            (exactRationalLiteral (-508992244893465839) 12800000000000000000),
            (exactRationalLiteral (-20266436196385541) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1688946349157141) 4915200000000000000),
            (exactRationalLiteral (-1688946349157141) 512000000000000000),
            (exactRationalLiteral (1688946349157141) 160000000000000000),
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
          (exactRationalLiteral (15200517142414269) 25600000000000000000),
          (exactRationalLiteral (2102260711640348969) 76800000000000000000),
          (exactRationalLiteral (5073414712359651749) 153600000000000000000),
          (exactRationalLiteral (9839029876417181) 150000000000000000),
          (exactRationalLiteral (461385333950033003) 6400000000000000000),
          (exactRationalLiteral (324223270135875077) 19200000000000000000),
          (exactRationalLiteral (20840599743699211) 15360000000000000000),
          (exactRationalLiteral (10707876860207959) 25600000000000000000),
          (exactRationalLiteral (96755277032377213) 19200000000000000000),
          (exactRationalLiteral (10503126248034043) 2400000000000000000),
          (exactRationalLiteral (103582634239331163) 6400000000000000000),
          (exactRationalLiteral (3618766443630317) 480000000000000000),
          (exactRationalLiteral (73823983782842263) 9600000000000000000),
          (exactRationalLiteral (2432094231114601) 4800000000000000000),
          (exactRationalLiteral (185890055848640177) 30720000000000000000),
          (exactRationalLiteral (12555542881055231) 614400000000000000),
          (exactRationalLiteral (2599487284682364617) 38400000000000000000),
          (exactRationalLiteral (4354332273517212883) 76800000000000000000),
          (exactRationalLiteral (3968591069393886889) 153600000000000000000),
          (exactRationalLiteral (20080977166556963) 4800000000000000000),
          (exactRationalLiteral (12796760512469847341) 76800000000000000000),
          (exactRationalLiteral (27222912154439232569) 76800000000000000000),
          (exactRationalLiteral (12796760512469847341) 76800000000000000000),
          (exactRationalLiteral (20080977166556963) 4800000000000000000),
          (exactRationalLiteral (3968591069393886889) 153600000000000000000),
          (exactRationalLiteral (4354332273517212883) 76800000000000000000),
          (exactRationalLiteral (2599487284682364617) 38400000000000000000),
          (exactRationalLiteral (12555542881055231) 614400000000000000),
          (exactRationalLiteral (185890055848640177) 30720000000000000000),
          (exactRationalLiteral (2432094231114601) 4800000000000000000),
          (exactRationalLiteral (73823983782842263) 9600000000000000000),
          (exactRationalLiteral (3618766443630317) 480000000000000000),
          (exactRationalLiteral (103582634239331163) 6400000000000000000),
          (exactRationalLiteral (10503126248034043) 2400000000000000000),
          (exactRationalLiteral (96755277032377213) 19200000000000000000),
          (exactRationalLiteral (10707876860207959) 25600000000000000000),
          (exactRationalLiteral (20840599743699211) 15360000000000000000),
          (exactRationalLiteral (324223270135875077) 19200000000000000000),
          (exactRationalLiteral (461385333950033003) 6400000000000000000),
          (exactRationalLiteral (9839029876417181) 150000000000000000),
          (exactRationalLiteral (5073414712359651749) 153600000000000000000),
          (exactRationalLiteral (2102260711640348969) 76800000000000000000),
          (exactRationalLiteral (15200517142414269) 25600000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 6),
      (37, 14)
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
            (exactRationalLiteral (15200517142414269) 204800000000000000000),
            (exactRationalLiteral (-15200517142414269) 12800000000000000000),
            (exactRationalLiteral (5066839047471423) 800000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (12143550670685514181) 614400000000000000000),
            (exactRationalLiteral (-550594386402836959) 12800000000000000000),
            (exactRationalLiteral (-534634558300019) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-5447403583152416269) 1228800000000000000000),
            (exactRationalLiteral (3653324060215463903) 25600000000000000000),
            (exactRationalLiteral (-131035002646255621) 1600000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-768990847598750313) 10240000000000000000),
            (exactRationalLiteral (-448236166427039231) 3200000000000000000),
            (exactRationalLiteral (40823983635054489) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (90911541610468443191) 1228800000000000000000),
            (exactRationalLiteral (451254323745912563) 25600000000000000000),
            (exactRationalLiteral (-338177570832135649) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-422313397042522553) 30720000000000000000),
            (exactRationalLiteral (110903853073809743) 3200000000000000000),
            (exactRationalLiteral (170292179745223) 1600000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (4949874905866787) 122880000000000000000),
            (exactRationalLiteral (-151087768956138997) 12800000000000000000),
            (exactRationalLiteral (-22654302354685097) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-99887066636102821) 409600000000000000000),
            (exactRationalLiteral (53581422537903141) 25600000000000000000),
            (exactRationalLiteral (11457411672614601) 1600000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2106044725048893473) 409600000000000000000),
            (exactRationalLiteral (38442911252644591) 25600000000000000000),
            (exactRationalLiteral (-3649573033501269) 1600000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (94286028531217113) 20480000000000000000),
            (exactRationalLiteral (4921224690651739) 1280000000000000000),
            (exactRationalLiteral (1349659838798631) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-20333566407610618519) 1228800000000000000000),
            (exactRationalLiteral (-154201447849354643) 25600000000000000000),
            (exactRationalLiteral (-5789090572282111) 1600000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-486296769579586511) 61440000000000000000),
            (exactRationalLiteral (-39526691073509963) 6400000000000000000),
            (exactRationalLiteral (-207175281046559) 80000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (5059214132264453831) 614400000000000000000),
            (exactRationalLiteral (115276626370896091) 12800000000000000000),
            (exactRationalLiteral (773589072482131) 160000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (187795646331874501) 307200000000000000000),
            (exactRationalLiteral (8267698504791761) 6400000000000000000),
            (exactRationalLiteral (-2502551842671251) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1327180252047299257) 245760000000000000000),
            (exactRationalLiteral (89757003379167631) 25600000000000000000),
            (exactRationalLiteral (2425326425781739) 1600000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (11100011364788134067) 614400000000000000000),
            (exactRationalLiteral (-143273241690949937) 12800000000000000000),
            (exactRationalLiteral (4649217422884763) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (18096030058060209661) 307200000000000000000),
            (exactRationalLiteral (-54484131155318699) 1280000000000000000),
            (exactRationalLiteral (1692531543600737) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-28430931079197747071) 614400000000000000000),
            (exactRationalLiteral (619511335709447037) 12800000000000000000),
            (exactRationalLiteral (-5403410137495051) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-30683122155580786577) 1228800000000000000000),
            (exactRationalLiteral (156481708449014283) 25600000000000000000),
            (exactRationalLiteral (77966770487459) 12800000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1356204621620681921) 307200000000000000000),
            (exactRationalLiteral (-22193038137635573) 6400000000000000000),
            (exactRationalLiteral (1458766519575751) 400000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-92325488385933395737) 614400000000000000000),
            (exactRationalLiteral (1047116981230990299) 12800000000000000000),
            (exactRationalLiteral (-22088976432145537) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (196466290505930464633) 614400000000000000000),
            (exactRationalLiteral (-445682656204829559) 2560000000000000000),
            (exactRationalLiteral (44629904934969073) 800000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-92325488385933395737) 614400000000000000000),
            (exactRationalLiteral (1047116981230990299) 12800000000000000000),
            (exactRationalLiteral (-22088976432145537) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1356204621620681921) 307200000000000000000),
            (exactRationalLiteral (-22193038137635573) 6400000000000000000),
            (exactRationalLiteral (1458766519575751) 400000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-30683122155580786577) 1228800000000000000000),
            (exactRationalLiteral (156481708449014283) 25600000000000000000),
            (exactRationalLiteral (77966770487459) 12800000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-28430931079197747071) 614400000000000000000),
            (exactRationalLiteral (619511335709447037) 12800000000000000000),
            (exactRationalLiteral (-5403410137495051) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (18096030058060209661) 307200000000000000000),
            (exactRationalLiteral (-54484131155318699) 1280000000000000000),
            (exactRationalLiteral (1692531543600737) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (11100011364788134067) 614400000000000000000),
            (exactRationalLiteral (-143273241690949937) 12800000000000000000),
            (exactRationalLiteral (4649217422884763) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1327180252047299257) 245760000000000000000),
            (exactRationalLiteral (89757003379167631) 25600000000000000000),
            (exactRationalLiteral (2425326425781739) 1600000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (187795646331874501) 307200000000000000000),
            (exactRationalLiteral (8267698504791761) 6400000000000000000),
            (exactRationalLiteral (-2502551842671251) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (5059214132264453831) 614400000000000000000),
            (exactRationalLiteral (115276626370896091) 12800000000000000000),
            (exactRationalLiteral (773589072482131) 160000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-486296769579586511) 61440000000000000000),
            (exactRationalLiteral (-39526691073509963) 6400000000000000000),
            (exactRationalLiteral (-207175281046559) 80000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-20333566407610618519) 1228800000000000000000),
            (exactRationalLiteral (-154201447849354643) 25600000000000000000),
            (exactRationalLiteral (-5789090572282111) 1600000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (94286028531217113) 20480000000000000000),
            (exactRationalLiteral (4921224690651739) 1280000000000000000),
            (exactRationalLiteral (1349659838798631) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (2106044725048893473) 409600000000000000000),
            (exactRationalLiteral (38442911252644591) 25600000000000000000),
            (exactRationalLiteral (-3649573033501269) 1600000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-99887066636102821) 409600000000000000000),
            (exactRationalLiteral (53581422537903141) 25600000000000000000),
            (exactRationalLiteral (11457411672614601) 1600000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4949874905866787) 122880000000000000000),
            (exactRationalLiteral (-151087768956138997) 12800000000000000000),
            (exactRationalLiteral (-22654302354685097) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-422313397042522553) 30720000000000000000),
            (exactRationalLiteral (110903853073809743) 3200000000000000000),
            (exactRationalLiteral (170292179745223) 1600000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (90911541610468443191) 1228800000000000000000),
            (exactRationalLiteral (451254323745912563) 25600000000000000000),
            (exactRationalLiteral (-338177570832135649) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-768990847598750313) 10240000000000000000),
            (exactRationalLiteral (-448236166427039231) 3200000000000000000),
            (exactRationalLiteral (40823983635054489) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-5447403583152416269) 1228800000000000000000),
            (exactRationalLiteral (3653324060215463903) 25600000000000000000),
            (exactRationalLiteral (-131035002646255621) 1600000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (12143550670685514181) 614400000000000000000),
            (exactRationalLiteral (-550594386402836959) 12800000000000000000),
            (exactRationalLiteral (-534634558300019) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (15200517142414269) 204800000000000000000),
            (exactRationalLiteral (-15200517142414269) 12800000000000000000),
            (exactRationalLiteral (5066839047471423) 800000000000000000),
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
          (exactRationalLiteral (87255986369454329) 6400000000000000000),
          (exactRationalLiteral (1593701866587623639) 19200000000000000000),
          (exactRationalLiteral (1911327327014969363) 25600000000000000000),
          (exactRationalLiteral (12409362072656053) 800000000000000000),
          (exactRationalLiteral (4156057259899573) 5120000000000000000),
          (exactRationalLiteral (6676054165352669) 19200000000000000000),
          (exactRationalLiteral (802754147752526449) 153600000000000000000),
          (exactRationalLiteral (186534831902618459) 38400000000000000000),
          (exactRationalLiteral (2601750198087918301) 153600000000000000000),
          (exactRationalLiteral (851057476767953) 102400000000000000),
          (exactRationalLiteral (45140841455012223) 5120000000000000000),
          (exactRationalLiteral (25615243852048379) 38400000000000000000),
          (exactRationalLiteral (107812830796529147) 19200000000000000000),
          (exactRationalLiteral (180395005502390561) 9600000000000000000),
          (exactRationalLiteral (295928212106314409) 4800000000000000000),
          (exactRationalLiteral (158198804621042241) 3200000000000000000),
          (exactRationalLiteral (97251193507846091) 3840000000000000000),
          (exactRationalLiteral (177309263183032963) 38400000000000000000),
          (exactRationalLiteral (1492721070318283697) 9600000000000000000),
          (exactRationalLiteral (3176367257806674139) 9600000000000000000),
          (exactRationalLiteral (1492721070318283697) 9600000000000000000),
          (exactRationalLiteral (177309263183032963) 38400000000000000000),
          (exactRationalLiteral (97251193507846091) 3840000000000000000),
          (exactRationalLiteral (158198804621042241) 3200000000000000000),
          (exactRationalLiteral (295928212106314409) 4800000000000000000),
          (exactRationalLiteral (180395005502390561) 9600000000000000000),
          (exactRationalLiteral (107812830796529147) 19200000000000000000),
          (exactRationalLiteral (25615243852048379) 38400000000000000000),
          (exactRationalLiteral (45140841455012223) 5120000000000000000),
          (exactRationalLiteral (851057476767953) 102400000000000000),
          (exactRationalLiteral (2601750198087918301) 153600000000000000000),
          (exactRationalLiteral (186534831902618459) 38400000000000000000),
          (exactRationalLiteral (802754147752526449) 153600000000000000000),
          (exactRationalLiteral (6676054165352669) 19200000000000000000),
          (exactRationalLiteral (4156057259899573) 5120000000000000000),
          (exactRationalLiteral (12409362072656053) 800000000000000000),
          (exactRationalLiteral (1911327327014969363) 25600000000000000000),
          (exactRationalLiteral (1593701866587623639) 19200000000000000000),
          (exactRationalLiteral (87255986369454329) 6400000000000000000),
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
      (37, 5),
      (37, 13)
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
            (exactRationalLiteral (1688946349157141) 614400000000000000000),
            (exactRationalLiteral (-1688946349157141) 12800000000000000000),
            (exactRationalLiteral (1688946349157141) 800000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (8912495944121234287) 614400000000000000000),
            (exactRationalLiteral (-513269321359865991) 12800000000000000000),
            (exactRationalLiteral (19197167079785503) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (4840489878655516771) 409600000000000000000),
            (exactRationalLiteral (2939858494421066727) 25600000000000000000),
            (exactRationalLiteral (-225697780250942967) 1600000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-13674517271673077741) 153600000000000000000),
            (exactRationalLiteral (-255002913261942039) 3200000000000000000),
            (exactRationalLiteral (55792642947494107) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (29739677056527328871) 409600000000000000000),
            (exactRationalLiteral (-1072408726270782117) 25600000000000000000),
            (exactRationalLiteral (-423653954176211691) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-391092423262963117) 51200000000000000000),
            (exactRationalLiteral (204764106627936471) 3200000000000000000),
            (exactRationalLiteral (25643604308910489) 200000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-234325824348440903) 122880000000000000000),
            (exactRationalLiteral (-250705105514121037) 12800000000000000000),
            (exactRationalLiteral (-27154365924305923) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (169190148017659459) 1228800000000000000000),
            (exactRationalLiteral (104348005541948477) 25600000000000000000),
            (exactRationalLiteral (13925879829408067) 1600000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6501148703989342393) 1228800000000000000000),
            (exactRationalLiteral (21920587983044343) 25600000000000000000),
            (exactRationalLiteral (-922317720259771) 320000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1579090105765544429) 307200000000000000000),
            (exactRationalLiteral (6097654462905843) 1280000000000000000),
            (exactRationalLiteral (1591414591836629) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-284426035682622303) 16384000000000000000),
            (exactRationalLiteral (-35842411489950719) 5120000000000000000),
            (exactRationalLiteral (-1343242845583473) 320000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2681081550959371241) 307200000000000000000),
            (exactRationalLiteral (-43673716573233827) 6400000000000000000),
            (exactRationalLiteral (-1037636344629137) 400000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1159862850387099953) 122880000000000000000),
            (exactRationalLiteral (5270436654756379) 512000000000000000),
            (exactRationalLiteral (4374199636596037) 800000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (206018131233778063) 307200000000000000000),
            (exactRationalLiteral (-2419050873289239) 6400000000000000000),
            (exactRationalLiteral (-2840822846369249) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1210251256760483611) 245760000000000000000),
            (exactRationalLiteral (863662628857123) 204800000000000000),
            (exactRationalLiteral (6675086188204633) 1600000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2056829928706037941) 122880000000000000000),
            (exactRationalLiteral (-130682812092841833) 12800000000000000000),
            (exactRationalLiteral (1645997376169289) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (16557253405935725111) 307200000000000000000),
            (exactRationalLiteral (-48294465989012531) 1280000000000000000),
            (exactRationalLiteral (1402301039552347) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-8336277894125999103) 204800000000000000000),
            (exactRationalLiteral (526060128365931317) 12800000000000000000),
            (exactRationalLiteral (-3941710596856521) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-29650864305029777827) 1228800000000000000000),
            (exactRationalLiteral (183673815755611059) 25600000000000000000),
            (exactRationalLiteral (3850207342366013) 1600000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1472391004126804883) 307200000000000000000),
            (exactRationalLiteral (-16624648016941837) 6400000000000000000),
            (exactRationalLiteral (1325428540771117) 400000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-86299516284154373483) 614400000000000000000),
            (exactRationalLiteral (962930041291821603) 12800000000000000000),
            (exactRationalLiteral (-20004493537438811) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (183614694192450569467) 614400000000000000000),
            (exactRationalLiteral (-2058231404561590139) 12800000000000000000),
            (exactRationalLiteral (8092206659261951) 160000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-86299516284154373483) 614400000000000000000),
            (exactRationalLiteral (962930041291821603) 12800000000000000000),
            (exactRationalLiteral (-20004493537438811) 800000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1472391004126804883) 307200000000000000000),
            (exactRationalLiteral (-16624648016941837) 6400000000000000000),
            (exactRationalLiteral (1325428540771117) 400000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-29650864305029777827) 1228800000000000000000),
            (exactRationalLiteral (183673815755611059) 25600000000000000000),
            (exactRationalLiteral (3850207342366013) 1600000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8336277894125999103) 204800000000000000000),
            (exactRationalLiteral (526060128365931317) 12800000000000000000),
            (exactRationalLiteral (-3941710596856521) 160000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (16557253405935725111) 307200000000000000000),
            (exactRationalLiteral (-48294465989012531) 1280000000000000000),
            (exactRationalLiteral (1402301039552347) 80000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (2056829928706037941) 122880000000000000000),
            (exactRationalLiteral (-130682812092841833) 12800000000000000000),
            (exactRationalLiteral (1645997376169289) 800000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1210251256760483611) 245760000000000000000),
            (exactRationalLiteral (863662628857123) 204800000000000000),
            (exactRationalLiteral (6675086188204633) 1600000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (206018131233778063) 307200000000000000000),
            (exactRationalLiteral (-2419050873289239) 6400000000000000000),
            (exactRationalLiteral (-2840822846369249) 400000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (1159862850387099953) 122880000000000000000),
            (exactRationalLiteral (5270436654756379) 512000000000000000),
            (exactRationalLiteral (4374199636596037) 800000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2681081550959371241) 307200000000000000000),
            (exactRationalLiteral (-43673716573233827) 6400000000000000000),
            (exactRationalLiteral (-1037636344629137) 400000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-284426035682622303) 16384000000000000000),
            (exactRationalLiteral (-35842411489950719) 5120000000000000000),
            (exactRationalLiteral (-1343242845583473) 320000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1579090105765544429) 307200000000000000000),
            (exactRationalLiteral (6097654462905843) 1280000000000000000),
            (exactRationalLiteral (1591414591836629) 400000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (6501148703989342393) 1228800000000000000000),
            (exactRationalLiteral (21920587983044343) 25600000000000000000),
            (exactRationalLiteral (-922317720259771) 320000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (169190148017659459) 1228800000000000000000),
            (exactRationalLiteral (104348005541948477) 25600000000000000000),
            (exactRationalLiteral (13925879829408067) 1600000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-234325824348440903) 122880000000000000000),
            (exactRationalLiteral (-250705105514121037) 12800000000000000000),
            (exactRationalLiteral (-27154365924305923) 800000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-391092423262963117) 51200000000000000000),
            (exactRationalLiteral (204764106627936471) 3200000000000000000),
            (exactRationalLiteral (25643604308910489) 200000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (29739677056527328871) 409600000000000000000),
            (exactRationalLiteral (-1072408726270782117) 25600000000000000000),
            (exactRationalLiteral (-423653954176211691) 1600000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-13674517271673077741) 153600000000000000000),
            (exactRationalLiteral (-255002913261942039) 3200000000000000000),
            (exactRationalLiteral (55792642947494107) 200000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (4840489878655516771) 409600000000000000000),
            (exactRationalLiteral (2939858494421066727) 25600000000000000000),
            (exactRationalLiteral (-225697780250942967) 1600000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8912495944121234287) 614400000000000000000),
            (exactRationalLiteral (-513269321359865991) 12800000000000000000),
            (exactRationalLiteral (19197167079785503) 800000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1688946349157141) 614400000000000000000),
            (exactRationalLiteral (-1688946349157141) 12800000000000000000),
            (exactRationalLiteral (1688946349157141) 800000000000000000),
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
          (exactRationalLiteral (1688946349157141) 76800000000000000000),
          (exactRationalLiteral (1312503688577643251) 76800000000000000000),
          (exactRationalLiteral (1104327167464579) 60000000000000000),
          (exactRationalLiteral (4643445232083399) 50000000000000000),
          (exactRationalLiteral (11401004209692216989) 153600000000000000000),
          (exactRationalLiteral (214102164708293263) 19200000000000000000),
          (exactRationalLiteral (245050972636999) 75000000000000000),
          (exactRationalLiteral (21372316007899) 50000000000000000),
          (exactRationalLiteral (533251521350153) 100000000000000000),
          (exactRationalLiteral (109078778897211) 20000000000000000),
          (exactRationalLiteral (5344287366469117) 300000000000000000),
          (exactRationalLiteral (2749234853205721) 300000000000000000),
          (exactRationalLiteral (3031236683148979) 300000000000000000),
          (exactRationalLiteral (2199050723454037) 3200000000000000000),
          (exactRationalLiteral (794653673867554591) 153600000000000000000),
          (exactRationalLiteral (1335329710245072601) 76800000000000000000),
          (exactRationalLiteral (720976270317679969) 12800000000000000000),
          (exactRationalLiteral (133248969876401177) 3072000000000000000),
          (exactRationalLiteral (1257807804616051241) 51200000000000000000),
          (exactRationalLiteral (37069221961541) 7500000000000000),
          (exactRationalLiteral (3718723422087062837) 25600000000000000000),
          (exactRationalLiteral (23739106992730449851) 76800000000000000000),
          (exactRationalLiteral (3718723422087062837) 25600000000000000000),
          (exactRationalLiteral (37069221961541) 7500000000000000),
          (exactRationalLiteral (1257807804616051241) 51200000000000000000),
          (exactRationalLiteral (133248969876401177) 3072000000000000000),
          (exactRationalLiteral (720976270317679969) 12800000000000000000),
          (exactRationalLiteral (1335329710245072601) 76800000000000000000),
          (exactRationalLiteral (794653673867554591) 153600000000000000000),
          (exactRationalLiteral (2199050723454037) 3200000000000000000),
          (exactRationalLiteral (3031236683148979) 300000000000000000),
          (exactRationalLiteral (2749234853205721) 300000000000000000),
          (exactRationalLiteral (5344287366469117) 300000000000000000),
          (exactRationalLiteral (109078778897211) 20000000000000000),
          (exactRationalLiteral (533251521350153) 100000000000000000),
          (exactRationalLiteral (21372316007899) 50000000000000000),
          (exactRationalLiteral (245050972636999) 75000000000000000),
          (exactRationalLiteral (214102164708293263) 19200000000000000000),
          (exactRationalLiteral (11401004209692216989) 153600000000000000000),
          (exactRationalLiteral (4643445232083399) 50000000000000000),
          (exactRationalLiteral (1104327167464579) 60000000000000000),
          (exactRationalLiteral (1312503688577643251) 76800000000000000000),
          (exactRationalLiteral (1688946349157141) 76800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 4),
      (37, 12)
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
            (exactRationalLiteral (50315400687740387531) 4915200000000000000000),
            (exactRationalLiteral (-1623077441540012501) 51200000000000000000),
            (exactRationalLiteral (52357336823871371) 1600000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (106167141395166989273) 4915200000000000000000),
            (exactRationalLiteral (4017273922120379689) 51200000000000000000),
            (exactRationalLiteral (-247716789592669063) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-891404756616697189177) 9830400000000000000000),
            (exactRationalLiteral (-1865321495977377913) 102400000000000000000),
            (exactRationalLiteral (921214714766080583) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (15667847193856309973) 245760000000000000000),
            (exactRationalLiteral (-1197636994076225199) 12800000000000000000),
            (exactRationalLiteral (-105460274135386247) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-8465609984940828997) 9830400000000000000000),
            (exactRationalLiteral (8911404583173452027) 102400000000000000000),
            (exactRationalLiteral (392099650136679227) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-875786885837880629) 245760000000000000000),
            (exactRationalLiteral (-323448759283294153) 12800000000000000000),
            (exactRationalLiteral (-475619122926577) 16000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-284837433955336003) 327680000000000000000),
            (exactRationalLiteral (254809294137445587) 51200000000000000000),
            (exactRationalLiteral (10942189910890131) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5208669936718390621) 9830400000000000000000),
            (exactRationalLiteral (-160019178111889411) 102400000000000000000),
            (exactRationalLiteral (-7941028614689123) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (32842047773168947927) 9830400000000000000000),
            (exactRationalLiteral (218099083423959639) 102400000000000000000),
            (exactRationalLiteral (4726048530467287) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1421000355030790387) 491520000000000000000),
            (exactRationalLiteral (7801374051509211) 5120000000000000000),
            (exactRationalLiteral (-322614735377713) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-130874032992486049627) 9830400000000000000000),
            (exactRationalLiteral (-327622876555224347) 102400000000000000000),
            (exactRationalLiteral (10864550876453) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-764310030281302061) 163840000000000000000),
            (exactRationalLiteral (-55069104832117227) 25600000000000000000),
            (exactRationalLiteral (-409950713602263) 160000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (5480136246271154241) 1638400000000000000000),
            (exactRationalLiteral (232516429925450739) 51200000000000000000),
            (exactRationalLiteral (281542459500807) 320000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7719771574409114167) 2457600000000000000000),
            (exactRationalLiteral (177616289630667769) 25600000000000000000),
            (exactRationalLiteral (-776716139117527) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-20824117028577919541) 1966080000000000000000),
            (exactRationalLiteral (1444545296695650999) 102400000000000000000),
            (exactRationalLiteral (-48271344178722697) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (172679285376372555511) 4915200000000000000000),
            (exactRationalLiteral (-1976520973650861673) 51200000000000000000),
            (exactRationalLiteral (46838685429712951) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (89855510901454592971) 819200000000000000000),
            (exactRationalLiteral (-477886711496470371) 5120000000000000000),
            (exactRationalLiteral (7012944387806349) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-571712427730640872043) 4915200000000000000000),
            (exactRationalLiteral (7463655943833016773) 51200000000000000000),
            (exactRationalLiteral (-29078064532971727) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-69934295557143156047) 3276800000000000000000),
            (exactRationalLiteral (-2191044974974168493) 102400000000000000000),
            (exactRationalLiteral (3727487189157771) 128000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2320351876145485907) 2457600000000000000000),
            (exactRationalLiteral (-276316922884565517) 25600000000000000000),
            (exactRationalLiteral (4584257774209427) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-383952561897402105407) 1638400000000000000000),
            (exactRationalLiteral (7048766472734366771) 51200000000000000000),
            (exactRationalLiteral (-70233989048125149) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2440185761537848001189) 4915200000000000000000),
            (exactRationalLiteral (-2935883200934907071) 10240000000000000000),
            (exactRationalLiteral (141370705353179621) 1600000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-383952561897402105407) 1638400000000000000000),
            (exactRationalLiteral (7048766472734366771) 51200000000000000000),
            (exactRationalLiteral (-70233989048125149) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2320351876145485907) 2457600000000000000000),
            (exactRationalLiteral (-276316922884565517) 25600000000000000000),
            (exactRationalLiteral (4584257774209427) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-69934295557143156047) 3276800000000000000000),
            (exactRationalLiteral (-2191044974974168493) 102400000000000000000),
            (exactRationalLiteral (3727487189157771) 128000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-571712427730640872043) 4915200000000000000000),
            (exactRationalLiteral (7463655943833016773) 51200000000000000000),
            (exactRationalLiteral (-29078064532971727) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (89855510901454592971) 819200000000000000000),
            (exactRationalLiteral (-477886711496470371) 5120000000000000000),
            (exactRationalLiteral (7012944387806349) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (172679285376372555511) 4915200000000000000000),
            (exactRationalLiteral (-1976520973650861673) 51200000000000000000),
            (exactRationalLiteral (46838685429712951) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-20824117028577919541) 1966080000000000000000),
            (exactRationalLiteral (1444545296695650999) 102400000000000000000),
            (exactRationalLiteral (-48271344178722697) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-7719771574409114167) 2457600000000000000000),
            (exactRationalLiteral (177616289630667769) 25600000000000000000),
            (exactRationalLiteral (-776716139117527) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (5480136246271154241) 1638400000000000000000),
            (exactRationalLiteral (232516429925450739) 51200000000000000000),
            (exactRationalLiteral (281542459500807) 320000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-764310030281302061) 163840000000000000000),
            (exactRationalLiteral (-55069104832117227) 25600000000000000000),
            (exactRationalLiteral (-409950713602263) 160000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-130874032992486049627) 9830400000000000000000),
            (exactRationalLiteral (-327622876555224347) 102400000000000000000),
            (exactRationalLiteral (10864550876453) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1421000355030790387) 491520000000000000000),
            (exactRationalLiteral (7801374051509211) 5120000000000000000),
            (exactRationalLiteral (-322614735377713) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (32842047773168947927) 9830400000000000000000),
            (exactRationalLiteral (218099083423959639) 102400000000000000000),
            (exactRationalLiteral (4726048530467287) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5208669936718390621) 9830400000000000000000),
            (exactRationalLiteral (-160019178111889411) 102400000000000000000),
            (exactRationalLiteral (-7941028614689123) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-284837433955336003) 327680000000000000000),
            (exactRationalLiteral (254809294137445587) 51200000000000000000),
            (exactRationalLiteral (10942189910890131) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-875786885837880629) 245760000000000000000),
            (exactRationalLiteral (-323448759283294153) 12800000000000000000),
            (exactRationalLiteral (-475619122926577) 16000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-8465609984940828997) 9830400000000000000000),
            (exactRationalLiteral (8911404583173452027) 102400000000000000000),
            (exactRationalLiteral (392099650136679227) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (15667847193856309973) 245760000000000000000),
            (exactRationalLiteral (-1197636994076225199) 12800000000000000000),
            (exactRationalLiteral (-105460274135386247) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-891404756616697189177) 9830400000000000000000),
            (exactRationalLiteral (-1865321495977377913) 102400000000000000000),
            (exactRationalLiteral (921214714766080583) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (106167141395166989273) 4915200000000000000000),
            (exactRationalLiteral (4017273922120379689) 51200000000000000000),
            (exactRationalLiteral (-247716789592669063) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (50315400687740387531) 4915200000000000000000),
            (exactRationalLiteral (-1623077441540012501) 51200000000000000000),
            (exactRationalLiteral (52357336823871371) 1600000000000000000),
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
          (exactRationalLiteral (14685709836696145489) 614400000000000000000),
          (exactRationalLiteral (22357110208728335621) 245760000000000000000),
          (exactRationalLiteral (9961948461846661) 150000000000000000),
          (exactRationalLiteral (172835218263647) 50000000000000000),
          (exactRationalLiteral (672846700042300009) 153600000000000000000),
          (exactRationalLiteral (1221170114801) 1200000000000000),
          (exactRationalLiteral (172841496311389) 300000000000000000),
          (exactRationalLiteral (1396251756718680413) 409600000000000000000),
          (exactRationalLiteral (60176461825808133) 20480000000000000000),
          (exactRationalLiteral (16482166573790863867) 1228800000000000000000),
          (exactRationalLiteral (1454500988673701839) 307200000000000000000),
          (exactRationalLiteral (2142804286577427467) 614400000000000000000),
          (exactRationalLiteral (62978984498723) 18750000000000000),
          (exactRationalLiteral (165712219154959) 15000000000000000),
          (exactRationalLiteral (1091008703391343) 30000000000000000),
          (exactRationalLiteral (16897018622979007) 150000000000000000),
          (exactRationalLiteral (12096012792541221) 100000000000000000),
          (exactRationalLiteral (27012425984581177997) 1228800000000000000000),
          (exactRationalLiteral (193061650824659) 150000000000000000),
          (exactRationalLiteral (71607405353942941) 300000000000000000),
          (exactRationalLiteral (75825506778068557) 150000000000000000),
          (exactRationalLiteral (71607405353942941) 300000000000000000),
          (exactRationalLiteral (193061650824659) 150000000000000000),
          (exactRationalLiteral (27012425984581177997) 1228800000000000000000),
          (exactRationalLiteral (12096012792541221) 100000000000000000),
          (exactRationalLiteral (16897018622979007) 150000000000000000),
          (exactRationalLiteral (1091008703391343) 30000000000000000),
          (exactRationalLiteral (165712219154959) 15000000000000000),
          (exactRationalLiteral (62978984498723) 18750000000000000),
          (exactRationalLiteral (2142804286577427467) 614400000000000000000),
          (exactRationalLiteral (1454500988673701839) 307200000000000000000),
          (exactRationalLiteral (16482166573790863867) 1228800000000000000000),
          (exactRationalLiteral (60176461825808133) 20480000000000000000),
          (exactRationalLiteral (1396251756718680413) 409600000000000000000),
          (exactRationalLiteral (172841496311389) 300000000000000000),
          (exactRationalLiteral (1221170114801) 1200000000000000),
          (exactRationalLiteral (672846700042300009) 153600000000000000000),
          (exactRationalLiteral (172835218263647) 50000000000000000),
          (exactRationalLiteral (9961948461846661) 150000000000000000),
          (exactRationalLiteral (22357110208728335621) 245760000000000000000),
          (exactRationalLiteral (14685709836696145489) 614400000000000000000),
          (exactRationalLiteral (1688946349157141) 150000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 63),
      (28, 15)
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
theorem generatorCoordinates26_valid : ∀ i, (generatorCoordinates26 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
