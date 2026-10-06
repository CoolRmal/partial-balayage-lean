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

/-- Actual coordinate interval candidates, block 17. -/
def generatorCoordinates17 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 3
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
            (exactRationalLiteral (841557586072382851) 9830400000000000000000),
            (exactRationalLiteral (-120222512296054693) 102400000000000000000),
            (exactRationalLiteral (17174644613722099) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (52137380577017898187) 3276800000000000000000),
            (exactRationalLiteral (-662226466340501547) 20480000000000000000),
            (exactRationalLiteral (-15018514552155087) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6284671273039805293) 1638400000000000000000),
            (exactRationalLiteral (5737132506578839377) 51200000000000000000),
            (exactRationalLiteral (-85316626447073751) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-114256557106405004569) 1966080000000000000000),
            (exactRationalLiteral (-11740648908724812869) 102400000000000000000),
            (exactRationalLiteral (478748389338998707) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (281833250072373971743) 4915200000000000000000),
            (exactRationalLiteral (958918885381178087) 51200000000000000000),
            (exactRationalLiteral (-261475228903289489) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-33826357361537033063) 3276800000000000000000),
            (exactRationalLiteral (2704937093866110339) 102400000000000000000),
            (exactRationalLiteral (272516440200518139) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-532603381654934227) 1228800000000000000000),
            (exactRationalLiteral (-124234851783384043) 12800000000000000000),
            (exactRationalLiteral (-8974910691759043) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-1758999170026439767) 1966080000000000000000),
            (exactRationalLiteral (29685912052145777) 20480000000000000000),
            (exactRationalLiteral (15653080025217373) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1438130329114056101) 3276800000000000000000),
            (exactRationalLiteral (-49203973312930759) 102400000000000000000),
            (exactRationalLiteral (-4203676431680607) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-2411522379184075897) 4915200000000000000000),
            (exactRationalLiteral (-683054683448481) 51200000000000000000),
            (exactRationalLiteral (485679020715767) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (70561040881078253) 1966080000000000000000),
            (exactRationalLiteral (10519796081710729) 102400000000000000000),
            (exactRationalLiteral (-207745156108367) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1085827169601744197) 819200000000000000000),
            (exactRationalLiteral (19734351738160031) 25600000000000000000),
            (exactRationalLiteral (92039837933487) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-4311652295327321) 245760000000000000000),
            (exactRationalLiteral (625328373814723) 2560000000000000000),
            (exactRationalLiteral (148842915233243) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-86554100571528662597) 9830400000000000000000),
            (exactRationalLiteral (-4752573900999113) 20480000000000000000),
            (exactRationalLiteral (-1311577430758613) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-49523229845668876709) 9830400000000000000000),
            (exactRationalLiteral (-27435385065110093) 102400000000000000000),
            (exactRationalLiteral (1953363038002123) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-59177087282881196461) 9830400000000000000000),
            (exactRationalLiteral (13160849747169379) 4096000000000000000),
            (exactRationalLiteral (4087618724390339) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-33364367878621454391) 1638400000000000000000),
            (exactRationalLiteral (138029684497600931) 51200000000000000000),
            (exactRationalLiteral (7415234231308203) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-32495152391044682461) 491520000000000000000),
            (exactRationalLiteral (-9163404004865609) 25600000000000000000),
            (exactRationalLiteral (3394023762709427) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-157858099494325569929) 393216000000000000000),
            (exactRationalLiteral (-7507419845245762793) 102400000000000000000),
            (exactRationalLiteral (1238111410648218703) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2759539216113063098469) 1638400000000000000000),
            (exactRationalLiteral (98128006518679110919) 51200000000000000000),
            (exactRationalLiteral (-3561414456409947489) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5079184461660352765267) 9830400000000000000000),
            (exactRationalLiteral (-639048877027839828683) 102400000000000000000),
            (exactRationalLiteral (11633970918603593981) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4896444282673667024653) 2457600000000000000000),
            (exactRationalLiteral (191770252260303688843) 25600000000000000000),
            (exactRationalLiteral (-1282239862573270813) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (219042144860052406883) 122880000000000000000),
            (exactRationalLiteral (-24749414223209035611) 6400000000000000000),
            (exactRationalLiteral (-206168085518167109) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-8772358244904713533403) 4915200000000000000000),
            (exactRationalLiteral (20630026758716322009) 10240000000000000000),
            (exactRationalLiteral (891895966366298773) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (6559700018063493422821) 2457600000000000000000),
            (exactRationalLiteral (-63875540544877221427) 25600000000000000000),
            (exactRationalLiteral (80535323885205809) 160000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-8772358244904713533403) 4915200000000000000000),
            (exactRationalLiteral (20630026758716322009) 10240000000000000000),
            (exactRationalLiteral (891895966366298773) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (219042144860052406883) 122880000000000000000),
            (exactRationalLiteral (-24749414223209035611) 6400000000000000000),
            (exactRationalLiteral (-206168085518167109) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-4896444282673667024653) 2457600000000000000000),
            (exactRationalLiteral (191770252260303688843) 25600000000000000000),
            (exactRationalLiteral (-1282239862573270813) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-5079184461660352765267) 9830400000000000000000),
            (exactRationalLiteral (-639048877027839828683) 102400000000000000000),
            (exactRationalLiteral (11633970918603593981) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2759539216113063098469) 1638400000000000000000),
            (exactRationalLiteral (98128006518679110919) 51200000000000000000),
            (exactRationalLiteral (-3561414456409947489) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-157858099494325569929) 393216000000000000000),
            (exactRationalLiteral (-7507419845245762793) 102400000000000000000),
            (exactRationalLiteral (1238111410648218703) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-32495152391044682461) 491520000000000000000),
            (exactRationalLiteral (-9163404004865609) 25600000000000000000),
            (exactRationalLiteral (3394023762709427) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-33364367878621454391) 1638400000000000000000),
            (exactRationalLiteral (138029684497600931) 51200000000000000000),
            (exactRationalLiteral (7415234231308203) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-59177087282881196461) 9830400000000000000000),
            (exactRationalLiteral (13160849747169379) 4096000000000000000),
            (exactRationalLiteral (4087618724390339) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-49523229845668876709) 9830400000000000000000),
            (exactRationalLiteral (-27435385065110093) 102400000000000000000),
            (exactRationalLiteral (1953363038002123) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-86554100571528662597) 9830400000000000000000),
            (exactRationalLiteral (-4752573900999113) 20480000000000000000),
            (exactRationalLiteral (-1311577430758613) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4311652295327321) 245760000000000000000),
            (exactRationalLiteral (625328373814723) 2560000000000000000),
            (exactRationalLiteral (148842915233243) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1085827169601744197) 819200000000000000000),
            (exactRationalLiteral (19734351738160031) 25600000000000000000),
            (exactRationalLiteral (92039837933487) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (70561040881078253) 1966080000000000000000),
            (exactRationalLiteral (10519796081710729) 102400000000000000000),
            (exactRationalLiteral (-207745156108367) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2411522379184075897) 4915200000000000000000),
            (exactRationalLiteral (-683054683448481) 51200000000000000000),
            (exactRationalLiteral (485679020715767) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1438130329114056101) 3276800000000000000000),
            (exactRationalLiteral (-49203973312930759) 102400000000000000000),
            (exactRationalLiteral (-4203676431680607) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-1758999170026439767) 1966080000000000000000),
            (exactRationalLiteral (29685912052145777) 20480000000000000000),
            (exactRationalLiteral (15653080025217373) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-532603381654934227) 1228800000000000000000),
            (exactRationalLiteral (-124234851783384043) 12800000000000000000),
            (exactRationalLiteral (-8974910691759043) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-33826357361537033063) 3276800000000000000000),
            (exactRationalLiteral (2704937093866110339) 102400000000000000000),
            (exactRationalLiteral (272516440200518139) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (281833250072373971743) 4915200000000000000000),
            (exactRationalLiteral (958918885381178087) 51200000000000000000),
            (exactRationalLiteral (-261475228903289489) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-114256557106405004569) 1966080000000000000000),
            (exactRationalLiteral (-11740648908724812869) 102400000000000000000),
            (exactRationalLiteral (478748389338998707) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6284671273039805293) 1638400000000000000000),
            (exactRationalLiteral (5737132506578839377) 51200000000000000000),
            (exactRationalLiteral (-85316626447073751) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (52137380577017898187) 3276800000000000000000),
            (exactRationalLiteral (-662226466340501547) 20480000000000000000),
            (exactRationalLiteral (-15018514552155087) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (841557586072382851) 9830400000000000000000),
            (exactRationalLiteral (-120222512296054693) 102400000000000000000),
            (exactRationalLiteral (17174644613722099) 3200000000000000000),
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
          (exactRationalLiteral (2453520659103157) 19200000000000000000),
          (exactRationalLiteral (324776999805565303) 19200000000000000000),
          (exactRationalLiteral (23634948363520501) 3200000000000000000),
          (exactRationalLiteral (75627661587366470873) 1228800000000000000000),
          (exactRationalLiteral (11829508111307968009) 204800000000000000000),
          (exactRationalLiteral (212482156668167711) 19200000000000000000),
          (exactRationalLiteral (23317251610201819) 30720000000000000000),
          (exactRationalLiteral (17957375147528957) 19200000000000000000),
          (exactRationalLiteral (559356784454906947) 1228800000000000000000),
          (exactRationalLiteral (75397634898098851) 153600000000000000000),
          (exactRationalLiteral (15988670751674447) 409600000000000000000),
          (exactRationalLiteral (414618979460400823) 307200000000000000000),
          (exactRationalLiteral (119160275566073) 4800000000000000000),
          (exactRationalLiteral (10828687703289489521) 1228800000000000000000),
          (exactRationalLiteral (2066645883967314331) 409600000000000000000),
          (exactRationalLiteral (39161327988194697) 6400000000000000000),
          (exactRationalLiteral (196260098877853037) 9600000000000000000),
          (exactRationalLiteral (5078205999482735977) 76800000000000000000),
          (exactRationalLiteral (495648546176584405661) 1228800000000000000000),
          (exactRationalLiteral (1070251093386680148227) 614400000000000000000),
          (exactRationalLiteral (57996696263978316089) 81920000000000000000),
          (exactRationalLiteral (10693230061486650211) 4800000000000000000),
          (exactRationalLiteral (3043514097925224753) 1600000000000000000),
          (exactRationalLiteral (5910609626279211677) 3200000000000000000),
          (exactRationalLiteral (4396127812802487809) 1600000000000000000),
          (exactRationalLiteral (5910609626279211677) 3200000000000000000),
          (exactRationalLiteral (3043514097925224753) 1600000000000000000),
          (exactRationalLiteral (10693230061486650211) 4800000000000000000),
          (exactRationalLiteral (57996696263978316089) 81920000000000000000),
          (exactRationalLiteral (1070251093386680148227) 614400000000000000000),
          (exactRationalLiteral (495648546176584405661) 1228800000000000000000),
          (exactRationalLiteral (5078205999482735977) 76800000000000000000),
          (exactRationalLiteral (196260098877853037) 9600000000000000000),
          (exactRationalLiteral (39161327988194697) 6400000000000000000),
          (exactRationalLiteral (2066645883967314331) 409600000000000000000),
          (exactRationalLiteral (10828687703289489521) 1228800000000000000000),
          (exactRationalLiteral (119160275566073) 4800000000000000000),
          (exactRationalLiteral (414618979460400823) 307200000000000000000),
          (exactRationalLiteral (15988670751674447) 409600000000000000000),
          (exactRationalLiteral (75397634898098851) 153600000000000000000),
          (exactRationalLiteral (559356784454906947) 1228800000000000000000),
          (exactRationalLiteral (17957375147528957) 19200000000000000000),
          (exactRationalLiteral (23317251610201819) 30720000000000000000),
          (exactRationalLiteral (212482156668167711) 19200000000000000000),
          (exactRationalLiteral (11829508111307968009) 204800000000000000000),
          (exactRationalLiteral (75627661587366470873) 1228800000000000000000),
          (exactRationalLiteral (23634948363520501) 3200000000000000000),
          (exactRationalLiteral (324776999805565303) 19200000000000000000),
          (exactRationalLiteral (2453520659103157) 19200000000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 51),
      (28, 3),
      (28, 19),
      (28, 35),
      (28, 51)
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
            (exactRationalLiteral (2453520659103157) 78643200000000000000),
            (exactRationalLiteral (-2453520659103157) 4096000000000000000),
            (exactRationalLiteral (2453520659103157) 640000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (136482399822655326059) 9830400000000000000000),
            (exactRationalLiteral (-3312569261689858607) 102400000000000000000),
            (exactRationalLiteral (14300049558479651) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (960022496556760637) 327680000000000000000),
            (exactRationalLiteral (1064708774694376293) 10240000000000000000),
            (exactRationalLiteral (-24295538021281041) 320000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-211868047727433442933) 3276800000000000000000),
            (exactRationalLiteral (-9636877786366024653) 102400000000000000000),
            (exactRationalLiteral (573137171840395401) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (284309969674490323829) 4915200000000000000000),
            (exactRationalLiteral (-156527511897601153) 51200000000000000000),
            (exactRationalLiteral (-296247969736100131) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-81863010891056281543) 9830400000000000000000),
            (exactRationalLiteral (3853123528644151867) 102400000000000000000),
            (exactRationalLiteral (2412614217508021) 25600000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1389370583278021201) 1228800000000000000000),
            (exactRationalLiteral (-32392815172251463) 2560000000000000000),
            (exactRationalLiteral (-9889701347177593) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-1541955050139295229) 1966080000000000000000),
            (exactRationalLiteral (214445019145968829) 102400000000000000000),
            (exactRationalLiteral (17354649417402599) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4661981656905945541) 9830400000000000000000),
            (exactRationalLiteral (-66980035292665887) 102400000000000000000),
            (exactRationalLiteral (-4684354558186957) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-803175642742930961) 1638400000000000000000),
            (exactRationalLiteral (278495360621387) 10240000000000000000),
            (exactRationalLiteral (552086722561941) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (413324965886262251) 9830400000000000000000),
            (exactRationalLiteral (9635778889230769) 102400000000000000000),
            (exactRationalLiteral (-234263440131613) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3376921314486942133) 2457600000000000000000),
            (exactRationalLiteral (4013423937733547) 5120000000000000000),
            (exactRationalLiteral (14868827464073) 160000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-905317625340263) 1228800000000000000000),
            (exactRationalLiteral (755100471406891) 2560000000000000000),
            (exactRationalLiteral (175587328747177) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-28904612809855889213) 3276800000000000000000),
            (exactRationalLiteral (-5944007029598833) 20480000000000000000),
            (exactRationalLiteral (-1667005390740687) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-49663004227326258391) 9830400000000000000000),
            (exactRationalLiteral (-18923146774474901) 102400000000000000000),
            (exactRationalLiteral (2302756107315473) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-19051538446380833253) 3276800000000000000000),
            (exactRationalLiteral (345018247062098723) 102400000000000000000),
            (exactRationalLiteral (782176593408357) 640000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19834830721544590091) 983040000000000000000),
            (exactRationalLiteral (168585176612888091) 51200000000000000000),
            (exactRationalLiteral (7862511826335377) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-162321528910244230619) 2457600000000000000000),
            (exactRationalLiteral (61503092872227791) 25600000000000000000),
            (exactRationalLiteral (3672625924999913) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-1325354441169260706297) 3276800000000000000000),
            (exactRationalLiteral (-2266801205626347153) 102400000000000000000),
            (exactRationalLiteral (1382197909161489117) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1764435858902779958401) 983040000000000000000),
            (exactRationalLiteral (82647638962816921439) 51200000000000000000),
            (exactRationalLiteral (-4178769321521147251) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8759265046318840300049) 9830400000000000000000),
            (exactRationalLiteral (-585210480110771297987) 102400000000000000000),
            (exactRationalLiteral (15285227539930671367) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3766553387951788106063) 2457600000000000000000),
            (exactRationalLiteral (36793884513095724647) 5120000000000000000),
            (exactRationalLiteral (-2618174984839261991) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (315096204938392164531) 204800000000000000000),
            (exactRationalLiteral (-25049890125088364971) 6400000000000000000),
            (exactRationalLiteral (55930134578502429) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-2715415756639583646211) 1638400000000000000000),
            (exactRationalLiteral (104971427973085479749) 51200000000000000000),
            (exactRationalLiteral (18751123385636079) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2060645895653865879901) 819200000000000000000),
            (exactRationalLiteral (-12387087540009101359) 5120000000000000000),
            (exactRationalLiteral (567374802989828271) 800000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2715415756639583646211) 1638400000000000000000),
            (exactRationalLiteral (104971427973085479749) 51200000000000000000),
            (exactRationalLiteral (18751123385636079) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (315096204938392164531) 204800000000000000000),
            (exactRationalLiteral (-25049890125088364971) 6400000000000000000),
            (exactRationalLiteral (55930134578502429) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-3766553387951788106063) 2457600000000000000000),
            (exactRationalLiteral (36793884513095724647) 5120000000000000000),
            (exactRationalLiteral (-2618174984839261991) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-8759265046318840300049) 9830400000000000000000),
            (exactRationalLiteral (-585210480110771297987) 102400000000000000000),
            (exactRationalLiteral (15285227539930671367) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1764435858902779958401) 983040000000000000000),
            (exactRationalLiteral (82647638962816921439) 51200000000000000000),
            (exactRationalLiteral (-4178769321521147251) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1325354441169260706297) 3276800000000000000000),
            (exactRationalLiteral (-2266801205626347153) 102400000000000000000),
            (exactRationalLiteral (1382197909161489117) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-162321528910244230619) 2457600000000000000000),
            (exactRationalLiteral (61503092872227791) 25600000000000000000),
            (exactRationalLiteral (3672625924999913) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-19834830721544590091) 983040000000000000000),
            (exactRationalLiteral (168585176612888091) 51200000000000000000),
            (exactRationalLiteral (7862511826335377) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-19051538446380833253) 3276800000000000000000),
            (exactRationalLiteral (345018247062098723) 102400000000000000000),
            (exactRationalLiteral (782176593408357) 640000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-49663004227326258391) 9830400000000000000000),
            (exactRationalLiteral (-18923146774474901) 102400000000000000000),
            (exactRationalLiteral (2302756107315473) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-28904612809855889213) 3276800000000000000000),
            (exactRationalLiteral (-5944007029598833) 20480000000000000000),
            (exactRationalLiteral (-1667005390740687) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-905317625340263) 1228800000000000000000),
            (exactRationalLiteral (755100471406891) 2560000000000000000),
            (exactRationalLiteral (175587328747177) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (3376921314486942133) 2457600000000000000000),
            (exactRationalLiteral (4013423937733547) 5120000000000000000),
            (exactRationalLiteral (14868827464073) 160000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (413324965886262251) 9830400000000000000000),
            (exactRationalLiteral (9635778889230769) 102400000000000000000),
            (exactRationalLiteral (-234263440131613) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-803175642742930961) 1638400000000000000000),
            (exactRationalLiteral (278495360621387) 10240000000000000000),
            (exactRationalLiteral (552086722561941) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4661981656905945541) 9830400000000000000000),
            (exactRationalLiteral (-66980035292665887) 102400000000000000000),
            (exactRationalLiteral (-4684354558186957) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-1541955050139295229) 1966080000000000000000),
            (exactRationalLiteral (214445019145968829) 102400000000000000000),
            (exactRationalLiteral (17354649417402599) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1389370583278021201) 1228800000000000000000),
            (exactRationalLiteral (-32392815172251463) 2560000000000000000),
            (exactRationalLiteral (-9889701347177593) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-81863010891056281543) 9830400000000000000000),
            (exactRationalLiteral (3853123528644151867) 102400000000000000000),
            (exactRationalLiteral (2412614217508021) 25600000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (284309969674490323829) 4915200000000000000000),
            (exactRationalLiteral (-156527511897601153) 51200000000000000000),
            (exactRationalLiteral (-296247969736100131) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-211868047727433442933) 3276800000000000000000),
            (exactRationalLiteral (-9636877786366024653) 102400000000000000000),
            (exactRationalLiteral (573137171840395401) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (960022496556760637) 327680000000000000000),
            (exactRationalLiteral (1064708774694376293) 10240000000000000000),
            (exactRationalLiteral (-24295538021281041) 320000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (136482399822655326059) 9830400000000000000000),
            (exactRationalLiteral (-3312569261689858607) 102400000000000000000),
            (exactRationalLiteral (14300049558479651) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2453520659103157) 78643200000000000000),
            (exactRationalLiteral (-2453520659103157) 4096000000000000000),
            (exactRationalLiteral (2453520659103157) 640000000000000000),
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
          (exactRationalLiteral (22081685931928413) 409600000000000000000),
          (exactRationalLiteral (18306043559293127933) 1228800000000000000000),
          (exactRationalLiteral (156189872221969649) 25600000000000000000),
          (exactRationalLiteral (10355440166166039347) 153600000000000000000),
          (exactRationalLiteral (5932194974702242079) 102400000000000000000),
          (exactRationalLiteral (11566522664239652689) 1228800000000000000000),
          (exactRationalLiteral (1190868318894397) 768000000000000000),
          (exactRationalLiteral (345912381024094477) 409600000000000000000),
          (exactRationalLiteral (25402162320425819) 51200000000000000000),
          (exactRationalLiteral (301510162790168869) 614400000000000000000),
          (exactRationalLiteral (6898691454555439) 153600000000000000000),
          (exactRationalLiteral (17902796136013541) 12800000000000000000),
          (exactRationalLiteral (488268121539961) 51200000000000000000),
          (exactRationalLiteral (1356377769768185363) 153600000000000000000),
          (exactRationalLiteral (1242817267569827) 245760000000000000),
          (exactRationalLiteral (7272231132943624537) 1228800000000000000000),
          (exactRationalLiteral (12457068155110015273) 614400000000000000000),
          (exactRationalLiteral (20306455663173955189) 307200000000000000000),
          (exactRationalLiteral (124368261433494580949) 307200000000000000000),
          (exactRationalLiteral (47173318885443914139) 25600000000000000000),
          (exactRationalLiteral (163550237120635916269) 153600000000000000000),
          (exactRationalLiteral (180235342210067031923) 102400000000000000000),
          (exactRationalLiteral (15944922288814511891) 9600000000000000000),
          (exactRationalLiteral (1057583591005795017287) 614400000000000000000),
          (exactRationalLiteral (796170471922365218161) 307200000000000000000),
          (exactRationalLiteral (1057583591005795017287) 614400000000000000000),
          (exactRationalLiteral (15944922288814511891) 9600000000000000000),
          (exactRationalLiteral (180235342210067031923) 102400000000000000000),
          (exactRationalLiteral (163550237120635916269) 153600000000000000000),
          (exactRationalLiteral (47173318885443914139) 25600000000000000000),
          (exactRationalLiteral (124368261433494580949) 307200000000000000000),
          (exactRationalLiteral (20306455663173955189) 307200000000000000000),
          (exactRationalLiteral (12457068155110015273) 614400000000000000000),
          (exactRationalLiteral (7272231132943624537) 1228800000000000000000),
          (exactRationalLiteral (1242817267569827) 245760000000000000),
          (exactRationalLiteral (1356377769768185363) 153600000000000000000),
          (exactRationalLiteral (488268121539961) 51200000000000000000),
          (exactRationalLiteral (17902796136013541) 12800000000000000000),
          (exactRationalLiteral (6898691454555439) 153600000000000000000),
          (exactRationalLiteral (301510162790168869) 614400000000000000000),
          (exactRationalLiteral (25402162320425819) 51200000000000000000),
          (exactRationalLiteral (345912381024094477) 409600000000000000000),
          (exactRationalLiteral (1190868318894397) 768000000000000000),
          (exactRationalLiteral (11566522664239652689) 1228800000000000000000),
          (exactRationalLiteral (5932194974702242079) 102400000000000000000),
          (exactRationalLiteral (10355440166166039347) 153600000000000000000),
          (exactRationalLiteral (156189872221969649) 25600000000000000000),
          (exactRationalLiteral (18306043559293127933) 1228800000000000000000),
          (exactRationalLiteral (22081685931928413) 409600000000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 50),
      (28, 2),
      (28, 18),
      (28, 34),
      (28, 50)
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
            (exactRationalLiteral (22081685931928413) 3276800000000000000000),
            (exactRationalLiteral (-22081685931928413) 102400000000000000000),
            (exactRationalLiteral (7360561977309471) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (116895859103660469181) 9830400000000000000000),
            (exactRationalLiteral (-3196731935234670527) 102400000000000000000),
            (exactRationalLiteral (43618613669114389) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (14913074717756170023) 1638400000000000000000),
            (exactRationalLiteral (4765310985727597737) 51200000000000000000),
            (exactRationalLiteral (-157638753765736659) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-686170208708406145129) 9830400000000000000000),
            (exactRationalLiteral (-7155551534001649661) 102400000000000000000),
            (exactRationalLiteral (133505190868358419) 640000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (93225579334313424257) 1638400000000000000000),
            (exactRationalLiteral (-1411064872507622961) 51200000000000000000),
            (exactRationalLiteral (-331020710568910773) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-55009107044977400897) 9830400000000000000000),
            (exactRationalLiteral (5117551311374131339) 102400000000000000000),
            (exactRationalLiteral (330637114176487111) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2483490617233370407) 1228800000000000000000),
            (exactRationalLiteral (-203352462560804787) 12800000000000000000),
            (exactRationalLiteral (-10804492002596143) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-2069347688414363693) 3276800000000000000000),
            (exactRationalLiteral (287266755599949677) 102400000000000000000),
            (exactRationalLiteral (762248752383513) 128000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5121996835866209747) 9830400000000000000000),
            (exactRationalLiteral (-17335761955685283) 20480000000000000000),
            (exactRationalLiteral (-5165032684693307) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-478856279186404657) 983040000000000000000),
            (exactRationalLiteral (3733639097047047) 51200000000000000000),
            (exactRationalLiteral (123698884881623) 320000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (6242965397386327) 131072000000000000000),
            (exactRationalLiteral (345827542426313) 4096000000000000000),
            (exactRationalLiteral (-260781724154859) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (699629075892868087) 491520000000000000000),
            (exactRationalLiteral (20329104836722951) 25600000000000000000),
            (exactRationalLiteral (56648436707243) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (7987240705296109) 409600000000000000000),
            (exactRationalLiteral (4531340499051031) 12800000000000000000),
            (exactRationalLiteral (202331742261111) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-86913584416984449169) 9830400000000000000000),
            (exactRationalLiteral (-37098912630921061) 102400000000000000000),
            (exactRationalLiteral (-2022433350722761) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-16582504154136022907) 3276800000000000000000),
            (exactRationalLiteral (-9013336206586309) 102400000000000000000),
            (exactRationalLiteral (2652149176628823) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-55038282204194800217) 9830400000000000000000),
            (exactRationalLiteral (72061661483113751) 20480000000000000000),
            (exactRationalLiteral (3734147209693231) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-98066503295749488689) 4915200000000000000000),
            (exactRationalLiteral (200929779108283947) 51200000000000000000),
            (exactRationalLiteral (8309789421362551) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-161726580754265059373) 2457600000000000000000),
            (exactRationalLiteral (137741632995130911) 25600000000000000000),
            (exactRationalLiteral (3951228087290399) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-3972501409837549250749) 9830400000000000000000),
            (exactRationalLiteral (3550163428046150143) 102400000000000000000),
            (exactRationalLiteral (1526284407674759531) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9265450476972102754579) 4915200000000000000000),
            (exactRationalLiteral (64697851946509932911) 51200000000000000000),
            (exactRationalLiteral (-4796124186632347013) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4024166723339663907341) 3276800000000000000000),
            (exactRationalLiteral (-516767056708394457747) 102400000000000000000),
            (exactRationalLiteral (18936484161257748753) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-899832897622017158419) 819200000000000000000),
            (exactRationalLiteral (34164970476317918583) 5120000000000000000),
            (exactRationalLiteral (-3954110107105253169) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (796708828559975011067) 614400000000000000000),
            (exactRationalLiteral (-24301973146581016179) 6400000000000000000),
            (exactRationalLiteral (318028354675171967) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-7519686267971533077967) 4915200000000000000000),
            (exactRationalLiteral (103300142780666698677) 51200000000000000000),
            (exactRationalLiteral (-170878743919005323) 320000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5817792351131457735089) 2457600000000000000000),
            (exactRationalLiteral (-59336542120958595259) 25600000000000000000),
            (exactRationalLiteral (732072986553627497) 800000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-7519686267971533077967) 4915200000000000000000),
            (exactRationalLiteral (103300142780666698677) 51200000000000000000),
            (exactRationalLiteral (-170878743919005323) 320000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (796708828559975011067) 614400000000000000000),
            (exactRationalLiteral (-24301973146581016179) 6400000000000000000),
            (exactRationalLiteral (318028354675171967) 200000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-899832897622017158419) 819200000000000000000),
            (exactRationalLiteral (34164970476317918583) 5120000000000000000),
            (exactRationalLiteral (-3954110107105253169) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-4024166723339663907341) 3276800000000000000000),
            (exactRationalLiteral (-516767056708394457747) 102400000000000000000),
            (exactRationalLiteral (18936484161257748753) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9265450476972102754579) 4915200000000000000000),
            (exactRationalLiteral (64697851946509932911) 51200000000000000000),
            (exactRationalLiteral (-4796124186632347013) 1600000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3972501409837549250749) 9830400000000000000000),
            (exactRationalLiteral (3550163428046150143) 102400000000000000000),
            (exactRationalLiteral (1526284407674759531) 3200000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-161726580754265059373) 2457600000000000000000),
            (exactRationalLiteral (137741632995130911) 25600000000000000000),
            (exactRationalLiteral (3951228087290399) 160000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-98066503295749488689) 4915200000000000000000),
            (exactRationalLiteral (200929779108283947) 51200000000000000000),
            (exactRationalLiteral (8309789421362551) 1600000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-55038282204194800217) 9830400000000000000000),
            (exactRationalLiteral (72061661483113751) 20480000000000000000),
            (exactRationalLiteral (3734147209693231) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-16582504154136022907) 3276800000000000000000),
            (exactRationalLiteral (-9013336206586309) 102400000000000000000),
            (exactRationalLiteral (2652149176628823) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-86913584416984449169) 9830400000000000000000),
            (exactRationalLiteral (-37098912630921061) 102400000000000000000),
            (exactRationalLiteral (-2022433350722761) 3200000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7987240705296109) 409600000000000000000),
            (exactRationalLiteral (4531340499051031) 12800000000000000000),
            (exactRationalLiteral (202331742261111) 400000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (699629075892868087) 491520000000000000000),
            (exactRationalLiteral (20329104836722951) 25600000000000000000),
            (exactRationalLiteral (56648436707243) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (6242965397386327) 131072000000000000000),
            (exactRationalLiteral (345827542426313) 4096000000000000000),
            (exactRationalLiteral (-260781724154859) 3200000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-478856279186404657) 983040000000000000000),
            (exactRationalLiteral (3733639097047047) 51200000000000000000),
            (exactRationalLiteral (123698884881623) 320000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5121996835866209747) 9830400000000000000000),
            (exactRationalLiteral (-17335761955685283) 20480000000000000000),
            (exactRationalLiteral (-5165032684693307) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-2069347688414363693) 3276800000000000000000),
            (exactRationalLiteral (287266755599949677) 102400000000000000000),
            (exactRationalLiteral (762248752383513) 128000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2483490617233370407) 1228800000000000000000),
            (exactRationalLiteral (-203352462560804787) 12800000000000000000),
            (exactRationalLiteral (-10804492002596143) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-55009107044977400897) 9830400000000000000000),
            (exactRationalLiteral (5117551311374131339) 102400000000000000000),
            (exactRationalLiteral (330637114176487111) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (93225579334313424257) 1638400000000000000000),
            (exactRationalLiteral (-1411064872507622961) 51200000000000000000),
            (exactRationalLiteral (-331020710568910773) 1600000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-686170208708406145129) 9830400000000000000000),
            (exactRationalLiteral (-7155551534001649661) 102400000000000000000),
            (exactRationalLiteral (133505190868358419) 640000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (14913074717756170023) 1638400000000000000000),
            (exactRationalLiteral (4765310985727597737) 51200000000000000000),
            (exactRationalLiteral (-157638753765736659) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (116895859103660469181) 9830400000000000000000),
            (exactRationalLiteral (-3196731935234670527) 102400000000000000000),
            (exactRationalLiteral (43618613669114389) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (22081685931928413) 3276800000000000000000),
            (exactRationalLiteral (-22081685931928413) 102400000000000000000),
            (exactRationalLiteral (7360561977309471) 3200000000000000000),
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
          (exactRationalLiteral (2453520659103157) 153600000000000000000),
          (exactRationalLiteral (131877345279496361) 10240000000000000000),
          (exactRationalLiteral (2439340013221851149) 204800000000000000000),
          (exactRationalLiteral (5879892425467791829) 81920000000000000000),
          (exactRationalLiteral (4420847763424575229) 76800000000000000000),
          (exactRationalLiteral (361376978151376697) 51200000000000000000),
          (exactRationalLiteral (390802359531410309) 153600000000000000000),
          (exactRationalLiteral (109586335317347957) 153600000000000000000),
          (exactRationalLiteral (674721087789852761) 1228800000000000000000),
          (exactRationalLiteral (37557188028138487) 76800000000000000000),
          (exactRationalLiteral (2466819330857359) 49152000000000000000),
          (exactRationalLiteral (444911723929290557) 307200000000000000000),
          (exactRationalLiteral (954402776164543) 30720000000000000000),
          (exactRationalLiteral (3626296923704557153) 409600000000000000000),
          (exactRationalLiteral (6220802665870410563) 1228800000000000000000),
          (exactRationalLiteral (876686192452089883) 153600000000000000000),
          (exactRationalLiteral (513773890122957117) 25600000000000000000),
          (exactRationalLiteral (2532519277146044099) 38400000000000000000),
          (exactRationalLiteral (62166329533561250903) 153600000000000000000),
          (exactRationalLiteral (1180605872852397489049) 614400000000000000000),
          (exactRationalLiteral (1695520782418717288789) 1228800000000000000000),
          (exactRationalLiteral (10072398789909384431) 7680000000000000000),
          (exactRationalLiteral (27201180748552976273) 19200000000000000000),
          (exactRationalLiteral (122370520391419186289) 76800000000000000000),
          (exactRationalLiteral (93717435115034570371) 38400000000000000000),
          (exactRationalLiteral (122370520391419186289) 76800000000000000000),
          (exactRationalLiteral (27201180748552976273) 19200000000000000000),
          (exactRationalLiteral (10072398789909384431) 7680000000000000000),
          (exactRationalLiteral (1695520782418717288789) 1228800000000000000000),
          (exactRationalLiteral (1180605872852397489049) 614400000000000000000),
          (exactRationalLiteral (62166329533561250903) 153600000000000000000),
          (exactRationalLiteral (2532519277146044099) 38400000000000000000),
          (exactRationalLiteral (513773890122957117) 25600000000000000000),
          (exactRationalLiteral (876686192452089883) 153600000000000000000),
          (exactRationalLiteral (6220802665870410563) 1228800000000000000000),
          (exactRationalLiteral (3626296923704557153) 409600000000000000000),
          (exactRationalLiteral (954402776164543) 30720000000000000000),
          (exactRationalLiteral (444911723929290557) 307200000000000000000),
          (exactRationalLiteral (2466819330857359) 49152000000000000000),
          (exactRationalLiteral (37557188028138487) 76800000000000000000),
          (exactRationalLiteral (674721087789852761) 1228800000000000000000),
          (exactRationalLiteral (109586335317347957) 153600000000000000000),
          (exactRationalLiteral (390802359531410309) 153600000000000000000),
          (exactRationalLiteral (361376978151376697) 51200000000000000000),
          (exactRationalLiteral (4420847763424575229) 76800000000000000000),
          (exactRationalLiteral (5879892425467791829) 81920000000000000000),
          (exactRationalLiteral (2439340013221851149) 204800000000000000000),
          (exactRationalLiteral (131877345279496361) 10240000000000000000),
          (exactRationalLiteral (2453520659103157) 153600000000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 49),
      (28, 1),
      (28, 17),
      (28, 33),
      (28, 49)
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
            (exactRationalLiteral (2453520659103157) 9830400000000000000000),
            (exactRationalLiteral (-2453520659103157) 102400000000000000000),
            (exactRationalLiteral (2453520659103157) 3200000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (32785388370908119213) 3276800000000000000000),
            (exactRationalLiteral (-592724070467388699) 20480000000000000000),
            (exactRationalLiteral (72937177779749127) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (23764926922602643589) 1638400000000000000000),
            (exactRationalLiteral (4062433843345988193) 51200000000000000000),
            (exactRationalLiteral (-193799817425068113) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-720715651330308951179) 9830400000000000000000),
            (exactRationalLiteral (-4296670151631687893) 102400000000000000000),
            (exactRationalLiteral (761914736843188789) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (267099009277736363161) 4915200000000000000000),
            (exactRationalLiteral (-2804693196448887337) 51200000000000000000),
            (exactRationalLiteral (-73158690280344283) 320000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6739970819554276529) 3276800000000000000000),
            (exactRationalLiteral (1299644088411209751) 20480000000000000000),
            (exactRationalLiteral (359697451164471597) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-767383691850205409) 245760000000000000000),
            (exactRationalLiteral (-248400011882026459) 12800000000000000000),
            (exactRationalLiteral (-11719282658014693) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-4248961628359598213) 9830400000000000000000),
            (exactRationalLiteral (366894769622671429) 102400000000000000000),
            (exactRationalLiteral (20757788201773051) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1901990933086371107) 3276800000000000000000),
            (exactRationalLiteral (-108300296770212343) 102400000000000000000),
            (exactRationalLiteral (-5645710811199657) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-2364191997449458927) 4915200000000000000000),
            (exactRationalLiteral (1268086439674371) 10240000000000000000),
            (exactRationalLiteral (684902126254289) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (516861082341970183) 9830400000000000000000),
            (exactRationalLiteral (7549525095991897) 102400000000000000000),
            (exactRationalLiteral (-57460001635621) 640000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1206909668974237523) 819200000000000000000),
            (exactRationalLiteral (20520307182325679) 25600000000000000000),
            (exactRationalLiteral (38952736094121) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (53684723671383581) 1228800000000000000000),
            (exactRationalLiteral (5394156295123343) 12800000000000000000),
            (exactRationalLiteral (45815231155009) 80000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-87161868804818576963) 9830400000000000000000),
            (exactRationalLiteral (-45899501953776253) 102400000000000000000),
            (exactRationalLiteral (-475572262140967) 640000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-49768369117250787299) 9830400000000000000000),
            (exactRationalLiteral (2294046638555683) 102400000000000000000),
            (exactRationalLiteral (3001542245942173) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-52832329536214463131) 9830400000000000000000),
            (exactRationalLiteral (374891424739644571) 102400000000000000000),
            (exactRationalLiteral (3557411452344677) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-32253139345887775233) 1638400000000000000000),
            (exactRationalLiteral (235063491983788499) 51200000000000000000),
            (exactRationalLiteral (350282680655589) 64000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-160657485227811040247) 2457600000000000000000),
            (exactRationalLiteral (219552216363843751) 25600000000000000000),
            (exactRationalLiteral (845966049916177) 32000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-3932308670383122153863) 9830400000000000000000),
            (exactRationalLiteral (1988694811154345819) 20480000000000000000),
            (exactRationalLiteral (334074181237605989) 640000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3197871559650376462947) 1638400000000000000000),
            (exactRationalLiteral (8855729093951629067) 10240000000000000000),
            (exactRationalLiteral (-216539162069741871) 64000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-597250386953958286957) 393216000000000000000),
            (exactRationalLiteral (-433718606820709307963) 102400000000000000000),
            (exactRationalLiteral (22587740782584826139) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1727342640350840920507) 2457600000000000000000),
            (exactRationalLiteral (152336541708636597883) 25600000000000000000),
            (exactRationalLiteral (-5290045229371244347) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (655761722816977655749) 614400000000000000000),
            (exactRationalLiteral (-4501132657537397847) 1280000000000000000),
            (exactRationalLiteral (116025314954368301) 40000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-6913630715294595856061) 4915200000000000000000),
            (exactRationalLiteral (98136278216325266829) 51200000000000000000),
            (exactRationalLiteral (-1727538562575689309) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (5471216766978604890403) 2457600000000000000000),
            (exactRationalLiteral (-56078853807616486819) 25600000000000000000),
            (exactRationalLiteral (896771170117426723) 800000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-6913630715294595856061) 4915200000000000000000),
            (exactRationalLiteral (98136278216325266829) 51200000000000000000),
            (exactRationalLiteral (-1727538562575689309) 1600000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (655761722816977655749) 614400000000000000000),
            (exactRationalLiteral (-4501132657537397847) 1280000000000000000),
            (exactRationalLiteral (116025314954368301) 40000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-1727342640350840920507) 2457600000000000000000),
            (exactRationalLiteral (152336541708636597883) 25600000000000000000),
            (exactRationalLiteral (-5290045229371244347) 800000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-597250386953958286957) 393216000000000000000),
            (exactRationalLiteral (-433718606820709307963) 102400000000000000000),
            (exactRationalLiteral (22587740782584826139) 3200000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3197871559650376462947) 1638400000000000000000),
            (exactRationalLiteral (8855729093951629067) 10240000000000000000),
            (exactRationalLiteral (-216539162069741871) 64000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3932308670383122153863) 9830400000000000000000),
            (exactRationalLiteral (1988694811154345819) 20480000000000000000),
            (exactRationalLiteral (334074181237605989) 640000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-160657485227811040247) 2457600000000000000000),
            (exactRationalLiteral (219552216363843751) 25600000000000000000),
            (exactRationalLiteral (845966049916177) 32000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-32253139345887775233) 1638400000000000000000),
            (exactRationalLiteral (235063491983788499) 51200000000000000000),
            (exactRationalLiteral (350282680655589) 64000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-52832329536214463131) 9830400000000000000000),
            (exactRationalLiteral (374891424739644571) 102400000000000000000),
            (exactRationalLiteral (3557411452344677) 3200000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-49768369117250787299) 9830400000000000000000),
            (exactRationalLiteral (2294046638555683) 102400000000000000000),
            (exactRationalLiteral (3001542245942173) 3200000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-87161868804818576963) 9830400000000000000000),
            (exactRationalLiteral (-45899501953776253) 102400000000000000000),
            (exactRationalLiteral (-475572262140967) 640000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (53684723671383581) 1228800000000000000000),
            (exactRationalLiteral (5394156295123343) 12800000000000000000),
            (exactRationalLiteral (45815231155009) 80000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1206909668974237523) 819200000000000000000),
            (exactRationalLiteral (20520307182325679) 25600000000000000000),
            (exactRationalLiteral (38952736094121) 800000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (516861082341970183) 9830400000000000000000),
            (exactRationalLiteral (7549525095991897) 102400000000000000000),
            (exactRationalLiteral (-57460001635621) 640000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2364191997449458927) 4915200000000000000000),
            (exactRationalLiteral (1268086439674371) 10240000000000000000),
            (exactRationalLiteral (684902126254289) 1600000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1901990933086371107) 3276800000000000000000),
            (exactRationalLiteral (-108300296770212343) 102400000000000000000),
            (exactRationalLiteral (-5645710811199657) 3200000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-4248961628359598213) 9830400000000000000000),
            (exactRationalLiteral (366894769622671429) 102400000000000000000),
            (exactRationalLiteral (20757788201773051) 3200000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-767383691850205409) 245760000000000000000),
            (exactRationalLiteral (-248400011882026459) 12800000000000000000),
            (exactRationalLiteral (-11719282658014693) 400000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-6739970819554276529) 3276800000000000000000),
            (exactRationalLiteral (1299644088411209751) 20480000000000000000),
            (exactRationalLiteral (359697451164471597) 3200000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (267099009277736363161) 4915200000000000000000),
            (exactRationalLiteral (-2804693196448887337) 51200000000000000000),
            (exactRationalLiteral (-73158690280344283) 320000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-720715651330308951179) 9830400000000000000000),
            (exactRationalLiteral (-4296670151631687893) 102400000000000000000),
            (exactRationalLiteral (761914736843188789) 3200000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (23764926922602643589) 1638400000000000000000),
            (exactRationalLiteral (4062433843345988193) 51200000000000000000),
            (exactRationalLiteral (-193799817425068113) 1600000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (32785388370908119213) 3276800000000000000000),
            (exactRationalLiteral (-592724070467388699) 20480000000000000000),
            (exactRationalLiteral (72937177779749127) 3200000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2453520659103157) 9830400000000000000000),
            (exactRationalLiteral (-2453520659103157) 102400000000000000000),
            (exactRationalLiteral (2453520659103157) 3200000000000000000),
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
          (exactRationalLiteral (2453520659103157) 1228800000000000000000),
          (exactRationalLiteral (13431397302627389767) 1228800000000000000000),
          (exactRationalLiteral (337250172175053) 20000000000000000),
          (exactRationalLiteral (22316672460431633) 300000000000000000),
          (exactRationalLiteral (34304136860411783281) 614400000000000000000),
          (exactRationalLiteral (4831251449978944163) 1228800000000000000000),
          (exactRationalLiteral (35230512528983) 9375000000000000),
          (exactRationalLiteral (132205583932959649) 245760000000000000000),
          (exactRationalLiteral (184571873811847) 300000000000000000),
          (exactRationalLiteral (99216324646530613) 204800000000000000000),
          (exactRationalLiteral (5479273462559) 100000000000000000),
          (exactRationalLiteral (449511467142049) 300000000000000000),
          (exactRationalLiteral (5742821714749) 100000000000000000),
          (exactRationalLiteral (1332197244393799) 150000000000000000),
          (exactRationalLiteral (38885539070000491) 7680000000000000000),
          (exactRationalLiteral (2247760133674903689) 409600000000000000000),
          (exactRationalLiteral (12179820118920379451) 614400000000000000000),
          (exactRationalLiteral (4031334773214114611) 61440000000000000000),
          (exactRationalLiteral (32976666859009415721) 81920000000000000000),
          (exactRationalLiteral (59264535527176621) 30000000000000000),
          (exactRationalLiteral (164416774939500601) 100000000000000000),
          (exactRationalLiteral (274944304200466431451) 307200000000000000000),
          (exactRationalLiteral (604073369411921511) 512000000000000000),
          (exactRationalLiteral (300532733050408683047) 204800000000000000000),
          (exactRationalLiteral (235085887200834363809) 102400000000000000000),
          (exactRationalLiteral (300532733050408683047) 204800000000000000000),
          (exactRationalLiteral (604073369411921511) 512000000000000000),
          (exactRationalLiteral (274944304200466431451) 307200000000000000000),
          (exactRationalLiteral (164416774939500601) 100000000000000000),
          (exactRationalLiteral (59264535527176621) 30000000000000000),
          (exactRationalLiteral (32976666859009415721) 81920000000000000000),
          (exactRationalLiteral (4031334773214114611) 61440000000000000000),
          (exactRationalLiteral (12179820118920379451) 614400000000000000000),
          (exactRationalLiteral (2247760133674903689) 409600000000000000000),
          (exactRationalLiteral (38885539070000491) 7680000000000000000),
          (exactRationalLiteral (1332197244393799) 150000000000000000),
          (exactRationalLiteral (5742821714749) 100000000000000000),
          (exactRationalLiteral (449511467142049) 300000000000000000),
          (exactRationalLiteral (5479273462559) 100000000000000000),
          (exactRationalLiteral (99216324646530613) 204800000000000000000),
          (exactRationalLiteral (184571873811847) 300000000000000000),
          (exactRationalLiteral (132205583932959649) 245760000000000000000),
          (exactRationalLiteral (35230512528983) 9375000000000000),
          (exactRationalLiteral (4831251449978944163) 1228800000000000000000),
          (exactRationalLiteral (34304136860411783281) 614400000000000000000),
          (exactRationalLiteral (22316672460431633) 300000000000000000),
          (exactRationalLiteral (337250172175053) 20000000000000000),
          (exactRationalLiteral (13431397302627389767) 1228800000000000000000),
          (exactRationalLiteral (2453520659103157) 1228800000000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 32),
      (28, 48)
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
            (exactRationalLiteral (16828698200788553863) 78643200000000000000000),
            (exactRationalLiteral (-885720957936239677) 409600000000000000000),
            (exactRationalLiteral (46616892522959983) 6400000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1445879886310842086413) 78643200000000000000000),
            (exactRationalLiteral (-503107079375359799) 16384000000000000000),
            (exactRationalLiteral (-103333439380897019) 6400000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-168532496145346178809) 13107200000000000000000),
            (exactRationalLiteral (24202849259515189353) 204800000000000000000),
            (exactRationalLiteral (-80230593745818867) 3200000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-253327359349213259863) 5242880000000000000000),
            (exactRationalLiteral (-55357703640411766941) 409600000000000000000),
            (exactRationalLiteral (721524822424505679) 6400000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2160082879422678330499) 39321600000000000000000),
            (exactRationalLiteral (8630520859180369103) 204800000000000000000),
            (exactRationalLiteral (-436018605724552373) 3200000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-935067607340526723377) 78643200000000000000000),
            (exactRationalLiteral (5732673783803884651) 409600000000000000000),
            (exactRationalLiteral (472382037931075063) 6400000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1904201865963371689) 9830400000000000000000),
            (exactRationalLiteral (-328876076491087187) 51200000000000000000),
            (exactRationalLiteral (-15662844744971711) 800000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-15404825299986058891) 15728640000000000000000),
            (exactRationalLiteral (60385251588176681) 81920000000000000000),
            (exactRationalLiteral (27052236569971681) 6400000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-32163398581806945059) 78643200000000000000000),
            (exactRationalLiteral (-118750841199440271) 409600000000000000000),
            (exactRationalLiteral (-7205657547095339) 6400000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-6394164793574573047) 13107200000000000000000),
            (exactRationalLiteral (-11615702875032089) 204800000000000000000),
            (exactRationalLiteral (805338786816099) 3200000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (432349897935136841) 15728640000000000000000),
            (exactRationalLiteral (45902608898719681) 409600000000000000000),
            (exactRationalLiteral (-349194602158619) 6400000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (24890702923130602043) 19660800000000000000000),
            (exactRationalLiteral (76875413936306359) 102400000000000000000),
            (exactRationalLiteral (228318927399779) 1600000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-67881938503428833) 1966080000000000000000),
            (exactRationalLiteral (394560573622151) 2048000000000000000),
            (exactRationalLiteral (230824796681651) 800000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-230393851589681493067) 26214400000000000000000),
            (exactRationalLiteral (-2930511156183437) 16384000000000000000),
            (exactRationalLiteral (-1734584961562041) 6400000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-394268548272576174017) 78643200000000000000000),
            (exactRationalLiteral (-144441387654065957) 409600000000000000000),
            (exactRationalLiteral (3033243402720871) 6400000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-164177928030103601571) 26214400000000000000000),
            (exactRationalLiteral (246424680652454839) 81920000000000000000),
            (exactRationalLiteral (8617076842152063) 6400000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-807942279871763929169) 39321600000000000000000),
            (exactRationalLiteral (409405023302079339) 204800000000000000000),
            (exactRationalLiteral (13712274475048471) 3200000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-51871913470207162741) 786432000000000000000),
            (exactRationalLiteral (-358643357147249761) 102400000000000000000),
            (exactRationalLiteral (6091542119692639) 320000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-2062964226847347654243) 5242880000000000000000),
            (exactRationalLiteral (-52990826362531545057) 409600000000000000000),
            (exactRationalLiteral (2116006575013261371) 6400000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (59845633306200725569891) 39321600000000000000000),
            (exactRationalLiteral (456023379389025396431) 204800000000000000000),
            (exactRationalLiteral (-5579441750041895573) 3200000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-773650972654835640631) 78643200000000000000000),
            (exactRationalLiteral (-2743234218716842727027) 409600000000000000000),
            (exactRationalLiteral (14139800283889494497) 6400000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-50786609431251923701129) 19660800000000000000000),
            (exactRationalLiteral (776026617264355281907) 102400000000000000000),
            (exactRationalLiteral (775358080518436319) 1600000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (679956286414058099967) 327680000000000000000),
            (exactRationalLiteral (-91598067431264431039) 25600000000000000000),
            (exactRationalLiteral (-1067581721278008063) 400000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-25393172679737122878533) 13107200000000000000000),
            (exactRationalLiteral (76769661061948436209) 40960000000000000000),
            (exactRationalLiteral (3966654040184254281) 3200000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (18786746811213915857771) 6553600000000000000000),
            (exactRationalLiteral (-261496967273481976283) 102400000000000000000),
            (exactRationalLiteral (15744311197702401) 64000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-25393172679737122878533) 13107200000000000000000),
            (exactRationalLiteral (76769661061948436209) 40960000000000000000),
            (exactRationalLiteral (3966654040184254281) 3200000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (679956286414058099967) 327680000000000000000),
            (exactRationalLiteral (-91598067431264431039) 25600000000000000000),
            (exactRationalLiteral (-1067581721278008063) 400000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-50786609431251923701129) 19660800000000000000000),
            (exactRationalLiteral (776026617264355281907) 102400000000000000000),
            (exactRationalLiteral (775358080518436319) 1600000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-773650972654835640631) 78643200000000000000000),
            (exactRationalLiteral (-2743234218716842727027) 409600000000000000000),
            (exactRationalLiteral (14139800283889494497) 6400000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (59845633306200725569891) 39321600000000000000000),
            (exactRationalLiteral (456023379389025396431) 204800000000000000000),
            (exactRationalLiteral (-5579441750041895573) 3200000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2062964226847347654243) 5242880000000000000000),
            (exactRationalLiteral (-52990826362531545057) 409600000000000000000),
            (exactRationalLiteral (2116006575013261371) 6400000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-51871913470207162741) 786432000000000000000),
            (exactRationalLiteral (-358643357147249761) 102400000000000000000),
            (exactRationalLiteral (6091542119692639) 320000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-807942279871763929169) 39321600000000000000000),
            (exactRationalLiteral (409405023302079339) 204800000000000000000),
            (exactRationalLiteral (13712274475048471) 3200000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-164177928030103601571) 26214400000000000000000),
            (exactRationalLiteral (246424680652454839) 81920000000000000000),
            (exactRationalLiteral (8617076842152063) 6400000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-394268548272576174017) 78643200000000000000000),
            (exactRationalLiteral (-144441387654065957) 409600000000000000000),
            (exactRationalLiteral (3033243402720871) 6400000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-230393851589681493067) 26214400000000000000000),
            (exactRationalLiteral (-2930511156183437) 16384000000000000000),
            (exactRationalLiteral (-1734584961562041) 6400000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-67881938503428833) 1966080000000000000000),
            (exactRationalLiteral (394560573622151) 2048000000000000000),
            (exactRationalLiteral (230824796681651) 800000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (24890702923130602043) 19660800000000000000000),
            (exactRationalLiteral (76875413936306359) 102400000000000000000),
            (exactRationalLiteral (228318927399779) 1600000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (432349897935136841) 15728640000000000000000),
            (exactRationalLiteral (45902608898719681) 409600000000000000000),
            (exactRationalLiteral (-349194602158619) 6400000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6394164793574573047) 13107200000000000000000),
            (exactRationalLiteral (-11615702875032089) 204800000000000000000),
            (exactRationalLiteral (805338786816099) 3200000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-32163398581806945059) 78643200000000000000000),
            (exactRationalLiteral (-118750841199440271) 409600000000000000000),
            (exactRationalLiteral (-7205657547095339) 6400000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-15404825299986058891) 15728640000000000000000),
            (exactRationalLiteral (60385251588176681) 81920000000000000000),
            (exactRationalLiteral (27052236569971681) 6400000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1904201865963371689) 9830400000000000000000),
            (exactRationalLiteral (-328876076491087187) 51200000000000000000),
            (exactRationalLiteral (-15662844744971711) 800000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-935067607340526723377) 78643200000000000000000),
            (exactRationalLiteral (5732673783803884651) 409600000000000000000),
            (exactRationalLiteral (472382037931075063) 6400000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2160082879422678330499) 39321600000000000000000),
            (exactRationalLiteral (8630520859180369103) 204800000000000000000),
            (exactRationalLiteral (-436018605724552373) 3200000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-253327359349213259863) 5242880000000000000000),
            (exactRationalLiteral (-55357703640411766941) 409600000000000000000),
            (exactRationalLiteral (721524822424505679) 6400000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-168532496145346178809) 13107200000000000000000),
            (exactRationalLiteral (24202849259515189353) 204800000000000000000),
            (exactRationalLiteral (-80230593745818867) 3200000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1445879886310842086413) 78643200000000000000000),
            (exactRationalLiteral (-503107079375359799) 16384000000000000000),
            (exactRationalLiteral (-103333439380897019) 6400000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (16828698200788553863) 78643200000000000000000),
            (exactRationalLiteral (-885720957936239677) 409600000000000000000),
            (exactRationalLiteral (46616892522959983) 6400000000000000000),
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
          (exactRationalLiteral (495471466537613747923) 9830400000000000000000),
          (exactRationalLiteral (91027041658859557307) 1638400000000000000000),
          (exactRationalLiteral (4952411524722078877) 409600000000000000000),
          (exactRationalLiteral (44442171195772303) 153600000000000000000),
          (exactRationalLiteral (243279997964809757) 245760000000000000000),
          (exactRationalLiteral (4067688552138725633) 9830400000000000000000),
          (exactRationalLiteral (2401861533642180503) 4915200000000000000000),
          (exactRationalLiteral (95766519725973157) 3276800000000000000000),
          (exactRationalLiteral (3140250659233926737) 2457600000000000000000),
          (exactRationalLiteral (5755041146179961) 153600000000000000000),
          (exactRationalLiteral (86425840571827864267) 9830400000000000000000),
          (exactRationalLiteral (657820996681325921) 131072000000000000000),
          (exactRationalLiteral (7753190854713945263) 1228800000000000000000),
          (exactRationalLiteral (842843314330252641) 40960000000000000000),
          (exactRationalLiteral (162222712148677462751) 2457600000000000000000),
          (exactRationalLiteral (3887126977352939128687) 9830400000000000000000),
          (exactRationalLiteral (7649582055210640059073) 4915200000000000000000),
          (exactRationalLiteral (373296191651792991647) 3276800000000000000000),
          (exactRationalLiteral (829870238144410956911) 307200000000000000000),
          (exactRationalLiteral (81803161751802987763) 38400000000000000000),
          (exactRationalLiteral (1208105100321852376321) 614400000000000000000),
          (exactRationalLiteral (892903590776722488791) 307200000000000000000),
          (exactRationalLiteral (1208105100321852376321) 614400000000000000000),
          (exactRationalLiteral (81803161751802987763) 38400000000000000000),
          (exactRationalLiteral (829870238144410956911) 307200000000000000000),
          (exactRationalLiteral (373296191651792991647) 3276800000000000000000),
          (exactRationalLiteral (7649582055210640059073) 4915200000000000000000),
          (exactRationalLiteral (3887126977352939128687) 9830400000000000000000),
          (exactRationalLiteral (162222712148677462751) 2457600000000000000000),
          (exactRationalLiteral (842843314330252641) 40960000000000000000),
          (exactRationalLiteral (7753190854713945263) 1228800000000000000000),
          (exactRationalLiteral (657820996681325921) 131072000000000000000),
          (exactRationalLiteral (86425840571827864267) 9830400000000000000000),
          (exactRationalLiteral (5755041146179961) 153600000000000000000),
          (exactRationalLiteral (3140250659233926737) 2457600000000000000000),
          (exactRationalLiteral (95766519725973157) 3276800000000000000000),
          (exactRationalLiteral (2401861533642180503) 4915200000000000000000),
          (exactRationalLiteral (4067688552138725633) 9830400000000000000000),
          (exactRationalLiteral (243279997964809757) 245760000000000000000),
          (exactRationalLiteral (44442171195772303) 153600000000000000000),
          (exactRationalLiteral (4952411524722078877) 409600000000000000000),
          (exactRationalLiteral (91027041658859557307) 1638400000000000000000),
          (exactRationalLiteral (495471466537613747923) 9830400000000000000000),
          (exactRationalLiteral (602529841108324891) 40960000000000000000),
          (exactRationalLiteral (7725459675332271161) 409600000000000000000),
          (exactRationalLiteral (2453520659103157) 9830400000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (13, 61),
      (14, 29)
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
            (exactRationalLiteral (12054146998173810341) 78643200000000000000000),
            (exactRationalLiteral (-709067470480812373) 409600000000000000000),
            (exactRationalLiteral (41709851204753669) 6400000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (456430365796136630429) 26214400000000000000000),
            (exactRationalLiteral (-517294944547452543) 16384000000000000000),
            (exactRationalLiteral (-74014875270262281) 6400000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-120495934752844850843) 13107200000000000000000),
            (exactRationalLiteral (23809604757213250977) 204800000000000000000),
            (exactRationalLiteral (-116391657405150321) 3200000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-4123020759081569844667) 78643200000000000000000),
            (exactRationalLiteral (-52282826785710950837) 409600000000000000000),
            (exactRationalLiteral (815913604925902373) 6400000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2206494690345734674073) 39321600000000000000000),
            (exactRationalLiteral (6816900954616538327) 204800000000000000000),
            (exactRationalLiteral (-94158269311472603) 640000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-298295579611526192257) 26214400000000000000000),
            (exactRationalLiteral (61442580876033231) 3276800000000000000),
            (exactRationalLiteral (501442374919059549) 6400000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-52133578508897233) 1966080000000000000000),
            (exactRationalLiteral (-393357036781811131) 51200000000000000000),
            (exactRationalLiteral (-16577635400390261) 800000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-74881135835876592949) 78643200000000000000000),
            (exactRationalLiteral (413538343005140581) 409600000000000000000),
            (exactRationalLiteral (28753805962156907) 6400000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-10988098077358252051) 26214400000000000000000),
            (exactRationalLiteral (-148534827640834327) 409600000000000000000),
            (exactRationalLiteral (-7686335673601689) 6400000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-19242258901724733791) 39321600000000000000000),
            (exactRationalLiteral (-1652306464815069) 40960000000000000000),
            (exactRationalLiteral (871746488662273) 3200000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2432868734706005879) 78643200000000000000000),
            (exactRationalLiteral (44452793922038713) 409600000000000000000),
            (exactRationalLiteral (-75142577236373) 1280000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8451541483691595019) 6553600000000000000000),
            (exactRationalLiteral (77753298244679231) 102400000000000000000),
            (exactRationalLiteral (210623226786657) 1600000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-277348731259585967) 9830400000000000000000),
            (exactRationalLiteral (10840802354308247) 51200000000000000000),
            (exactRationalLiteral (51513842039117) 160000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-691643368173850667539) 78643200000000000000000),
            (exactRationalLiteral (-80911974670798237) 409600000000000000000),
            (exactRationalLiteral (-418002584308823) 1280000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-395097400105390665907) 78643200000000000000000),
            (exactRationalLiteral (-131609627904555773) 409600000000000000000),
            (exactRationalLiteral (3382636472034221) 6400000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-485038345691660729003) 78643200000000000000000),
            (exactRationalLiteral (1266238239116185339) 409600000000000000000),
            (exactRationalLiteral (8440341084803509) 6400000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-268439837775956920929) 13107200000000000000000),
            (exactRationalLiteral (465148676392327571) 204800000000000000000),
            (exactRationalLiteral (2831910414015129) 640000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1298578632327635199031) 19660800000000000000000),
            (exactRationalLiteral (-234026493130492121) 102400000000000000000),
            (exactRationalLiteral (10192230851173) 512000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-31236439935991191865879) 78643200000000000000000),
            (exactRationalLiteral (-8847725413090391749) 81920000000000000000),
            (exactRationalLiteral (452018614705306357) 1280000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (20837450287357976800851) 13107200000000000000000),
            (exactRationalLiteral (86494180531727082923) 40960000000000000000),
            (exactRationalLiteral (-1239359323030619067) 640000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3409754731012781951857) 15728640000000000000000),
            (exactRationalLiteral (-2679372504338630594267) 409600000000000000000),
            (exactRationalLiteral (17791056905216571883) 6400000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-46126489171188634738571) 19660800000000000000000),
            (exactRationalLiteral (776456179341897044827) 102400000000000000000),
            (exactRationalLiteral (-560577041747554859) 1600000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (9637993303848335494667) 4915200000000000000000),
            (exactRationalLiteral (-19068839575236624843) 5120000000000000000),
            (exactRationalLiteral (-32219340047253541) 16000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-73832320938242627148733) 39321600000000000000000),
            (exactRationalLiteral (397968631784517872781) 204800000000000000000),
            (exactRationalLiteral (3093509197203591587) 3200000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (54796640716094421632819) 19660800000000000000000),
            (exactRationalLiteral (-259593139786584137731) 102400000000000000000),
            (exactRationalLiteral (558305963506359251) 1600000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-73832320938242627148733) 39321600000000000000000),
            (exactRationalLiteral (397968631784517872781) 204800000000000000000),
            (exactRationalLiteral (3093509197203591587) 3200000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (9637993303848335494667) 4915200000000000000000),
            (exactRationalLiteral (-19068839575236624843) 5120000000000000000),
            (exactRationalLiteral (-32219340047253541) 16000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-46126489171188634738571) 19660800000000000000000),
            (exactRationalLiteral (776456179341897044827) 102400000000000000000),
            (exactRationalLiteral (-560577041747554859) 1600000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-3409754731012781951857) 15728640000000000000000),
            (exactRationalLiteral (-2679372504338630594267) 409600000000000000000),
            (exactRationalLiteral (17791056905216571883) 6400000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (20837450287357976800851) 13107200000000000000000),
            (exactRationalLiteral (86494180531727082923) 40960000000000000000),
            (exactRationalLiteral (-1239359323030619067) 640000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-31236439935991191865879) 78643200000000000000000),
            (exactRationalLiteral (-8847725413090391749) 81920000000000000000),
            (exactRationalLiteral (452018614705306357) 1280000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1298578632327635199031) 19660800000000000000000),
            (exactRationalLiteral (-234026493130492121) 102400000000000000000),
            (exactRationalLiteral (10192230851173) 512000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-268439837775956920929) 13107200000000000000000),
            (exactRationalLiteral (465148676392327571) 204800000000000000000),
            (exactRationalLiteral (2831910414015129) 640000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-485038345691660729003) 78643200000000000000000),
            (exactRationalLiteral (1266238239116185339) 409600000000000000000),
            (exactRationalLiteral (8440341084803509) 6400000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-395097400105390665907) 78643200000000000000000),
            (exactRationalLiteral (-131609627904555773) 409600000000000000000),
            (exactRationalLiteral (3382636472034221) 6400000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-691643368173850667539) 78643200000000000000000),
            (exactRationalLiteral (-80911974670798237) 409600000000000000000),
            (exactRationalLiteral (-418002584308823) 1280000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-277348731259585967) 9830400000000000000000),
            (exactRationalLiteral (10840802354308247) 51200000000000000000),
            (exactRationalLiteral (51513842039117) 160000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (8451541483691595019) 6553600000000000000000),
            (exactRationalLiteral (77753298244679231) 102400000000000000000),
            (exactRationalLiteral (210623226786657) 1600000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (2432868734706005879) 78643200000000000000000),
            (exactRationalLiteral (44452793922038713) 409600000000000000000),
            (exactRationalLiteral (-75142577236373) 1280000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19242258901724733791) 39321600000000000000000),
            (exactRationalLiteral (-1652306464815069) 40960000000000000000),
            (exactRationalLiteral (871746488662273) 3200000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-10988098077358252051) 26214400000000000000000),
            (exactRationalLiteral (-148534827640834327) 409600000000000000000),
            (exactRationalLiteral (-7686335673601689) 6400000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-74881135835876592949) 78643200000000000000000),
            (exactRationalLiteral (413538343005140581) 409600000000000000000),
            (exactRationalLiteral (28753805962156907) 6400000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-52133578508897233) 1966080000000000000000),
            (exactRationalLiteral (-393357036781811131) 51200000000000000000),
            (exactRationalLiteral (-16577635400390261) 800000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-298295579611526192257) 26214400000000000000000),
            (exactRationalLiteral (61442580876033231) 3276800000000000000),
            (exactRationalLiteral (501442374919059549) 6400000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2206494690345734674073) 39321600000000000000000),
            (exactRationalLiteral (6816900954616538327) 204800000000000000000),
            (exactRationalLiteral (-94158269311472603) 640000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4123020759081569844667) 78643200000000000000000),
            (exactRationalLiteral (-52282826785710950837) 409600000000000000000),
            (exactRationalLiteral (815913604925902373) 6400000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-120495934752844850843) 13107200000000000000000),
            (exactRationalLiteral (23809604757213250977) 204800000000000000000),
            (exactRationalLiteral (-116391657405150321) 3200000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (456430365796136630429) 26214400000000000000000),
            (exactRationalLiteral (-517294944547452543) 16384000000000000000),
            (exactRationalLiteral (-74014875270262281) 6400000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (12054146998173810341) 78643200000000000000000),
            (exactRationalLiteral (-709067470480812373) 409600000000000000000),
            (exactRationalLiteral (41709851204753669) 6400000000000000000),
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
          (exactRationalLiteral (596205520162067151) 3276800000000000000000),
          (exactRationalLiteral (7039257571608013639) 393216000000000000000),
          (exactRationalLiteral (18051988040440003779) 1638400000000000000000),
          (exactRationalLiteral (348093611998101749) 6400000000000000000),
          (exactRationalLiteral (543338777538939403) 9600000000000000000),
          (exactRationalLiteral (114554738713353481499) 9830400000000000000000),
          (exactRationalLiteral (363996412211621) 2400000000000000000),
          (exactRationalLiteral (3168180842987568191) 3276800000000000000000),
          (exactRationalLiteral (8162401870381181) 19200000000000000000),
          (exactRationalLiteral (313548096604493) 640000000000000000),
          (exactRationalLiteral (25049674987027) 768000000000000000),
          (exactRationalLiteral (312359709077623) 240000000000000000),
          (exactRationalLiteral (2575931690822341) 81920000000000000000),
          (exactRationalLiteral (56306360013884089) 6400000000000000000),
          (exactRationalLiteral (96553199800574603) 19200000000000000000),
          (exactRationalLiteral (61101456377234525027) 9830400000000000000000),
          (exactRationalLiteral (100834088042454379019) 4915200000000000000000),
          (exactRationalLiteral (317183706820652149) 4800000000000000000),
          (exactRationalLiteral (2552270792213355429) 6400000000000000000),
          (exactRationalLiteral (15573941528997026797) 9600000000000000000),
          (exactRationalLiteral (6111253019788449289) 19200000000000000000),
          (exactRationalLiteral (403807262273153629517) 163840000000000000000),
          (exactRationalLiteral (1240184799732911564621) 614400000000000000000),
          (exactRationalLiteral (9377063716697884957621) 4915200000000000000000),
          (exactRationalLiteral (6947126588031613903019) 2457600000000000000000),
          (exactRationalLiteral (9377063716697884957621) 4915200000000000000000),
          (exactRationalLiteral (1240184799732911564621) 614400000000000000000),
          (exactRationalLiteral (403807262273153629517) 163840000000000000000),
          (exactRationalLiteral (6111253019788449289) 19200000000000000000),
          (exactRationalLiteral (15573941528997026797) 9600000000000000000),
          (exactRationalLiteral (2552270792213355429) 6400000000000000000),
          (exactRationalLiteral (317183706820652149) 4800000000000000000),
          (exactRationalLiteral (100834088042454379019) 4915200000000000000000),
          (exactRationalLiteral (61101456377234525027) 9830400000000000000000),
          (exactRationalLiteral (96553199800574603) 19200000000000000000),
          (exactRationalLiteral (56306360013884089) 6400000000000000000),
          (exactRationalLiteral (2575931690822341) 81920000000000000000),
          (exactRationalLiteral (312359709077623) 240000000000000000),
          (exactRationalLiteral (25049674987027) 768000000000000000),
          (exactRationalLiteral (313548096604493) 640000000000000000),
          (exactRationalLiteral (8162401870381181) 19200000000000000000),
          (exactRationalLiteral (3168180842987568191) 3276800000000000000000),
          (exactRationalLiteral (363996412211621) 2400000000000000000),
          (exactRationalLiteral (114554738713353481499) 9830400000000000000000),
          (exactRationalLiteral (543338777538939403) 9600000000000000000),
          (exactRationalLiteral (348093611998101749) 6400000000000000000),
          (exactRationalLiteral (18051988040440003779) 1638400000000000000000),
          (exactRationalLiteral (7039257571608013639) 393216000000000000000),
          (exactRationalLiteral (596205520162067151) 3276800000000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (13, 60),
      (14, 28)
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
        lower := (exactRationalLiteral (3) 4)
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
            (exactRationalLiteral (22081685931928413) 209715200000000000000),
            (exactRationalLiteral (-22081685931928413) 16384000000000000000),
            (exactRationalLiteral (7360561977309471) 1280000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1290925951459491401417) 78643200000000000000000),
            (exactRationalLiteral (-13169795986546093223) 409600000000000000000),
            (exactRationalLiteral (-44696311159627543) 6400000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-14678101323916945089) 2621440000000000000000),
            (exactRationalLiteral (4654343200054797357) 40960000000000000000),
            (exactRationalLiteral (-6102108842579271) 128000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-4426549201406719134437) 78643200000000000000000),
            (exactRationalLiteral (-48830394801004547957) 409600000000000000000),
            (exactRationalLiteral (910302387427299067) 6400000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (747202502983804768429) 13107200000000000000000),
            (exactRationalLiteral (4864190086721464983) 204800000000000000000),
            (exactRationalLiteral (-505564087390173657) 3200000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-842671253330573000989) 78643200000000000000000),
            (exactRationalLiteral (9744212783156361043) 409600000000000000000),
            (exactRationalLiteral (106100542381408807) 1280000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2823400900661710283) 9830400000000000000000),
            (exactRationalLiteral (-18459886387768371) 2048000000000000000),
            (exactRationalLiteral (-17492426055808811) 800000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-960640717716415009) 1048576000000000000000),
            (exactRationalLiteral (531956705638138661) 409600000000000000000),
            (exactRationalLiteral (30455375354342133) 6400000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-33949661938509007783) 78643200000000000000000),
            (exactRationalLiteral (-180241526588253783) 409600000000000000000),
            (exactRationalLiteral (-8167013800108039) 6400000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-19281101506997853889) 39321600000000000000000),
            (exactRationalLiteral (-928346193146781) 40960000000000000000),
            (exactRationalLiteral (938154190508447) 3200000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (898323623489320931) 26214400000000000000000),
            (exactRationalLiteral (42896905809264761) 409600000000000000000),
            (exactRationalLiteral (-402231170205111) 6400000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (25823600936461847839) 19660800000000000000000),
            (exactRationalLiteral (15712079950119923) 20480000000000000000),
            (exactRationalLiteral (38585505234707) 320000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-69702036319111243) 3276800000000000000000),
            (exactRationalLiteral (2384913604423691) 10240000000000000000),
            (exactRationalLiteral (284313623709519) 800000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-692155341888773914637) 78643200000000000000000),
            (exactRationalLiteral (-17996576455387769) 81920000000000000000),
            (exactRationalLiteral (-2445440881526189) 6400000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-131948356220958778831) 26214400000000000000000),
            (exactRationalLiteral (-117380295877792189) 409600000000000000000),
            (exactRationalLiteral (3732029541347571) 6400000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-477340339106975369077) 78643200000000000000000),
            (exactRationalLiteral (1299646131940702267) 409600000000000000000),
            (exactRationalLiteral (1652721065490991) 1280000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-32094276701371831237) 1572864000000000000000),
            (exactRationalLiteral (522681439862684499) 204800000000000000000),
            (exactRationalLiteral (14606829665102819) 3200000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1299595010586253354537) 19660800000000000000000),
            (exactRationalLiteral (-103837585867924761) 102400000000000000000),
            (exactRationalLiteral (6648746444273611) 320000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-31474174235507532155273) 78643200000000000000000),
            (exactRationalLiteral (-34910081774319290777) 409600000000000000000),
            (exactRationalLiteral (2404179572039802199) 6400000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2601213811967338437887) 1572864000000000000000),
            (exactRationalLiteral (406449006467800633751) 204800000000000000000),
            (exactRationalLiteral (-6814151480264295097) 3200000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-10965636990582595384249) 26214400000000000000000),
            (exactRationalLiteral (-2600905763475110151963) 409600000000000000000),
            (exactRationalLiteral (21442313526543649269) 6400000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-13826607586709095697543) 6553600000000000000000),
            (exactRationalLiteral (154308400186074968607) 20480000000000000000),
            (exactRationalLiteral (-1896512164013546037) 1600000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (9057310707457447365229) 4915200000000000000000),
            (exactRationalLiteral (-98041935440715139239) 25600000000000000000),
            (exactRationalLiteral (-543385281084668987) 400000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-71410879616540999463779) 39321600000000000000000),
            (exactRationalLiteral (408596378887370913741) 204800000000000000000),
            (exactRationalLiteral (2220364354222928893) 3200000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (53246440341671248314349) 19660800000000000000000),
            (exactRationalLiteral (-10281220782617244091) 4096000000000000000),
            (exactRationalLiteral (723004147070158477) 1600000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-71410879616540999463779) 39321600000000000000000),
            (exactRationalLiteral (408596378887370913741) 204800000000000000000),
            (exactRationalLiteral (2220364354222928893) 3200000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (9057310707457447365229) 4915200000000000000000),
            (exactRationalLiteral (-98041935440715139239) 25600000000000000000),
            (exactRationalLiteral (-543385281084668987) 400000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-13826607586709095697543) 6553600000000000000000),
            (exactRationalLiteral (154308400186074968607) 20480000000000000000),
            (exactRationalLiteral (-1896512164013546037) 1600000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-10965636990582595384249) 26214400000000000000000),
            (exactRationalLiteral (-2600905763475110151963) 409600000000000000000),
            (exactRationalLiteral (21442313526543649269) 6400000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2601213811967338437887) 1572864000000000000000),
            (exactRationalLiteral (406449006467800633751) 204800000000000000000),
            (exactRationalLiteral (-6814151480264295097) 3200000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-31474174235507532155273) 78643200000000000000000),
            (exactRationalLiteral (-34910081774319290777) 409600000000000000000),
            (exactRationalLiteral (2404179572039802199) 6400000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1299595010586253354537) 19660800000000000000000),
            (exactRationalLiteral (-103837585867924761) 102400000000000000000),
            (exactRationalLiteral (6648746444273611) 320000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-32094276701371831237) 1572864000000000000000),
            (exactRationalLiteral (522681439862684499) 204800000000000000000),
            (exactRationalLiteral (14606829665102819) 3200000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-477340339106975369077) 78643200000000000000000),
            (exactRationalLiteral (1299646131940702267) 409600000000000000000),
            (exactRationalLiteral (1652721065490991) 1280000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-131948356220958778831) 26214400000000000000000),
            (exactRationalLiteral (-117380295877792189) 409600000000000000000),
            (exactRationalLiteral (3732029541347571) 6400000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-692155341888773914637) 78643200000000000000000),
            (exactRationalLiteral (-17996576455387769) 81920000000000000000),
            (exactRationalLiteral (-2445440881526189) 6400000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-69702036319111243) 3276800000000000000000),
            (exactRationalLiteral (2384913604423691) 10240000000000000000),
            (exactRationalLiteral (284313623709519) 800000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (25823600936461847839) 19660800000000000000000),
            (exactRationalLiteral (15712079950119923) 20480000000000000000),
            (exactRationalLiteral (38585505234707) 320000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (898323623489320931) 26214400000000000000000),
            (exactRationalLiteral (42896905809264761) 409600000000000000000),
            (exactRationalLiteral (-402231170205111) 6400000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19281101506997853889) 39321600000000000000000),
            (exactRationalLiteral (-928346193146781) 40960000000000000000),
            (exactRationalLiteral (938154190508447) 3200000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-33949661938509007783) 78643200000000000000000),
            (exactRationalLiteral (-180241526588253783) 409600000000000000000),
            (exactRationalLiteral (-8167013800108039) 6400000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-960640717716415009) 1048576000000000000000),
            (exactRationalLiteral (531956705638138661) 409600000000000000000),
            (exactRationalLiteral (30455375354342133) 6400000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2823400900661710283) 9830400000000000000000),
            (exactRationalLiteral (-18459886387768371) 2048000000000000000),
            (exactRationalLiteral (-17492426055808811) 800000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-842671253330573000989) 78643200000000000000000),
            (exactRationalLiteral (9744212783156361043) 409600000000000000000),
            (exactRationalLiteral (106100542381408807) 1280000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (747202502983804768429) 13107200000000000000000),
            (exactRationalLiteral (4864190086721464983) 204800000000000000000),
            (exactRationalLiteral (-505564087390173657) 3200000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4426549201406719134437) 78643200000000000000000),
            (exactRationalLiteral (-48830394801004547957) 409600000000000000000),
            (exactRationalLiteral (910302387427299067) 6400000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-14678101323916945089) 2621440000000000000000),
            (exactRationalLiteral (4654343200054797357) 40960000000000000000),
            (exactRationalLiteral (-6102108842579271) 128000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1290925951459491401417) 78643200000000000000000),
            (exactRationalLiteral (-13169795986546093223) 409600000000000000000),
            (exactRationalLiteral (-44696311159627543) 6400000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (22081685931928413) 209715200000000000000),
            (exactRationalLiteral (-22081685931928413) 16384000000000000000),
            (exactRationalLiteral (7360561977309471) 1280000000000000000),
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
          (exactRationalLiteral (2453520659103157) 19200000000000000000),
          (exactRationalLiteral (324776999805565303) 19200000000000000000),
          (exactRationalLiteral (23634948363520501) 3200000000000000000),
          (exactRationalLiteral (114256557106405004569) 1966080000000000000000),
          (exactRationalLiteral (281833250072373971743) 4915200000000000000000),
          (exactRationalLiteral (212482156668167711) 19200000000000000000),
          (exactRationalLiteral (532603381654934227) 1228800000000000000000),
          (exactRationalLiteral (17957375147528957) 19200000000000000000),
          (exactRationalLiteral (1438130329114056101) 3276800000000000000000),
          (exactRationalLiteral (2411522379184075897) 4915200000000000000000),
          (exactRationalLiteral (70561040881078253) 1966080000000000000000),
          (exactRationalLiteral (1085827169601744197) 819200000000000000000),
          (exactRationalLiteral (119160275566073) 4800000000000000000),
          (exactRationalLiteral (86554100571528662597) 9830400000000000000000),
          (exactRationalLiteral (49523229845668876709) 9830400000000000000000),
          (exactRationalLiteral (39161327988194697) 6400000000000000000),
          (exactRationalLiteral (196260098877853037) 9600000000000000000),
          (exactRationalLiteral (32495152391044682461) 491520000000000000000),
          (exactRationalLiteral (157858099494325569929) 393216000000000000000),
          (exactRationalLiteral (2759539216113063098469) 1638400000000000000000),
          (exactRationalLiteral (5079184461660352765267) 9830400000000000000000),
          (exactRationalLiteral (10693230061486650211) 4800000000000000000),
          (exactRationalLiteral (3043514097925224753) 1600000000000000000),
          (exactRationalLiteral (5910609626279211677) 3200000000000000000),
          (exactRationalLiteral (4396127812802487809) 1600000000000000000),
          (exactRationalLiteral (5910609626279211677) 3200000000000000000),
          (exactRationalLiteral (3043514097925224753) 1600000000000000000),
          (exactRationalLiteral (10693230061486650211) 4800000000000000000),
          (exactRationalLiteral (5079184461660352765267) 9830400000000000000000),
          (exactRationalLiteral (2759539216113063098469) 1638400000000000000000),
          (exactRationalLiteral (157858099494325569929) 393216000000000000000),
          (exactRationalLiteral (32495152391044682461) 491520000000000000000),
          (exactRationalLiteral (196260098877853037) 9600000000000000000),
          (exactRationalLiteral (39161327988194697) 6400000000000000000),
          (exactRationalLiteral (49523229845668876709) 9830400000000000000000),
          (exactRationalLiteral (86554100571528662597) 9830400000000000000000),
          (exactRationalLiteral (119160275566073) 4800000000000000000),
          (exactRationalLiteral (1085827169601744197) 819200000000000000000),
          (exactRationalLiteral (70561040881078253) 1966080000000000000000),
          (exactRationalLiteral (2411522379184075897) 4915200000000000000000),
          (exactRationalLiteral (1438130329114056101) 3276800000000000000000),
          (exactRationalLiteral (17957375147528957) 19200000000000000000),
          (exactRationalLiteral (532603381654934227) 1228800000000000000000),
          (exactRationalLiteral (212482156668167711) 19200000000000000000),
          (exactRationalLiteral (281833250072373971743) 4915200000000000000000),
          (exactRationalLiteral (114256557106405004569) 1966080000000000000000),
          (exactRationalLiteral (23634948363520501) 3200000000000000000),
          (exactRationalLiteral (324776999805565303) 19200000000000000000),
          (exactRationalLiteral (2453520659103157) 19200000000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (18, 0),
      (17, 36),
      (17, 8),
      (16, 44),
      (16, 12),
      (15, 44),
      (15, 12),
      (14, 44),
      (14, 12),
      (13, 44),
      (13, 12),
      (12, 44),
      (12, 12),
      (11, 44),
      (11, 12),
      (10, 44),
      (10, 12),
      (9, 44),
      (9, 12),
      (8, 44),
      (8, 12),
      (7, 44),
      (7, 12),
      (6, 44),
      (6, 12),
      (5, 44),
      (5, 12),
      (4, 44),
      (4, 12),
      (3, 44),
      (3, 27),
      (3, 59),
      (4, 27),
      (4, 59),
      (5, 27),
      (5, 59),
      (6, 27),
      (6, 59),
      (7, 27),
      (7, 59),
      (8, 27),
      (8, 59),
      (9, 27),
      (9, 59),
      (10, 27),
      (10, 59),
      (11, 27),
      (11, 59),
      (12, 27),
      (12, 59),
      (13, 27),
      (13, 59),
      (14, 27)
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
        lower := (exactRationalLiteral (25) 32)
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
            (exactRationalLiteral (5390384888049635929) 78643200000000000000000),
            (exactRationalLiteral (-414644991388433533) 409600000000000000000),
            (exactRationalLiteral (31895768568341041) 6400000000000000000),
            (exactRationalLiteral (-2453520659103157) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (242297618812548370103) 15728640000000000000000),
            (exactRationalLiteral (-13289944102963333919) 409600000000000000000),
            (exactRationalLiteral (-3075549409798561) 1280000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-27505500254840454247) 13107200000000000000000),
            (exactRationalLiteral (22589182988697396777) 204800000000000000000),
            (exactRationalLiteral (-188713784723813229) 3200000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1569410128811204415533) 26214400000000000000000),
            (exactRationalLiteral (-45000407686292558301) 409600000000000000000),
            (exactRationalLiteral (1004691169928695761) 6400000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2264586789459729768733) 39321600000000000000000),
            (exactRationalLiteral (2772388255495149071) 204800000000000000000),
            (exactRationalLiteral (-540336828222984299) 3200000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-777723702740798368367) 78643200000000000000000),
            (exactRationalLiteral (2384868860952101231) 81920000000000000000),
            (exactRationalLiteral (559563048895028521) 6400000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1161190426823669173) 1966080000000000000000),
            (exactRationalLiteral (-533296445228281619) 51200000000000000000),
            (exactRationalLiteral (-18407216711227361) 800000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-68484042813081447209) 78643200000000000000000),
            (exactRationalLiteral (131436269167975529) 81920000000000000000),
            (exactRationalLiteral (32156944746527359) 6400000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-35131037976145852349) 78643200000000000000000),
            (exactRationalLiteral (-213870938041698639) 409600000000000000000),
            (exactRationalLiteral (-8647691926614389) 6400000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-6432476137232923753) 13107200000000000000000),
            (exactRationalLiteral (-756298800007769) 204800000000000000000),
            (exactRationalLiteral (1004561892354621) 3200000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2947419458144997043) 78643200000000000000000),
            (exactRationalLiteral (1649397782415913) 16384000000000000000),
            (exactRationalLiteral (-428749454228357) 6400000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (26297207682477075461) 19660800000000000000000),
            (exactRationalLiteral (79296718454067511) 102400000000000000000),
            (exactRationalLiteral (175231825560413) 1600000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-26807991937210607) 1966080000000000000000),
            (exactRationalLiteral (13115311343984399) 51200000000000000000),
            (exactRationalLiteral (311058037223453) 800000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-230908668728284596757) 26214400000000000000000),
            (exactRationalLiteral (-100475501723007749) 409600000000000000000),
            (exactRationalLiteral (-2800868841508263) 6400000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3172025348090957323) 629145600000000000000),
            (exactRationalLiteral (-20350678314755041) 81920000000000000000),
            (exactRationalLiteral (4081422610660921) 6400000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-156481335331477030077) 26214400000000000000000),
            (exactRationalLiteral (1332347081735824979) 409600000000000000000),
            (exactRationalLiteral (8086869570106401) 6400000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-799043757828758331407) 39321600000000000000000),
            (exactRationalLiteral (582003313713150123) 204800000000000000000),
            (exactRationalLiteral (15054107260129993) 3200000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1299813539271558676723) 19660800000000000000000),
            (exactRationalLiteral (31923364640452319) 102400000000000000000),
            (exactRationalLiteral (6927348606564097) 320000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-10551402741764972397297) 26214400000000000000000),
            (exactRationalLiteral (-25005190489133541153) 409600000000000000000),
            (exactRationalLiteral (2548266070553072613) 6400000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (67384800100766648409469) 39321600000000000000000),
            (exactRationalLiteral (377957690816521053839) 204800000000000000000),
            (exactRationalLiteral (-7431506345375494859) 3200000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-48230432763794614963753) 78643200000000000000000),
            (exactRationalLiteral (-501566799225256280023) 81920000000000000000),
            (exactRationalLiteral (5018714029574145331) 1280000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1475146905640090582063) 786432000000000000000),
            (exactRationalLiteral (761284082029788676531) 102400000000000000000),
            (exactRationalLiteral (-646489457255907443) 320000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (2821195621440175726701) 1638400000000000000000),
            (exactRationalLiteral (-99691280124860476111) 25600000000000000000),
            (exactRationalLiteral (-281287060987999449) 400000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-22978716516779340495131) 13107200000000000000000),
            (exactRationalLiteral (16629261864732052157) 8192000000000000000),
            (exactRationalLiteral (1347219511242266199) 3200000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (17237864022259252933109) 6553600000000000000000),
            (exactRationalLiteral (-50761821322004573983) 20480000000000000000),
            (exactRationalLiteral (887702330633957703) 1600000000000000000),
            (exactRationalLiteral (82349091781899613) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-22978716516779340495131) 13107200000000000000000),
            (exactRationalLiteral (16629261864732052157) 8192000000000000000),
            (exactRationalLiteral (1347219511242266199) 3200000000000000000),
            (exactRationalLiteral (-436572421490331347) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2821195621440175726701) 1638400000000000000000),
            (exactRationalLiteral (-99691280124860476111) 25600000000000000000),
            (exactRationalLiteral (-281287060987999449) 400000000000000000),
            (exactRationalLiteral (131049110048334769) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-1475146905640090582063) 786432000000000000000),
            (exactRationalLiteral (761284082029788676531) 102400000000000000000),
            (exactRationalLiteral (-646489457255907443) 320000000000000000),
            (exactRationalLiteral (-667967561132995589) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-48230432763794614963753) 78643200000000000000000),
            (exactRationalLiteral (-501566799225256280023) 81920000000000000000),
            (exactRationalLiteral (5018714029574145331) 1280000000000000000),
            (exactRationalLiteral (1825628310663538693) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (67384800100766648409469) 39321600000000000000000),
            (exactRationalLiteral (377957690816521053839) 204800000000000000000),
            (exactRationalLiteral (-7431506345375494859) 3200000000000000000),
            (exactRationalLiteral (-308677432555599881) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-10551402741764972397297) 26214400000000000000000),
            (exactRationalLiteral (-25005190489133541153) 409600000000000000000),
            (exactRationalLiteral (2548266070553072613) 6400000000000000000),
            (exactRationalLiteral (72043249256635207) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1299813539271558676723) 19660800000000000000000),
            (exactRationalLiteral (31923364640452319) 102400000000000000000),
            (exactRationalLiteral (6927348606564097) 320000000000000000),
            (exactRationalLiteral (46433693715081) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-799043757828758331407) 39321600000000000000000),
            (exactRationalLiteral (582003313713150123) 204800000000000000000),
            (exactRationalLiteral (15054107260129993) 3200000000000000000),
            (exactRationalLiteral (223638797513587) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-156481335331477030077) 26214400000000000000000),
            (exactRationalLiteral (1332347081735824979) 409600000000000000000),
            (exactRationalLiteral (8086869570106401) 6400000000000000000),
            (exactRationalLiteral (-88367878674277) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3172025348090957323) 629145600000000000000),
            (exactRationalLiteral (-20350678314755041) 81920000000000000000),
            (exactRationalLiteral (4081422610660921) 6400000000000000000),
            (exactRationalLiteral (6987861386267) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-230908668728284596757) 26214400000000000000000),
            (exactRationalLiteral (-100475501723007749) 409600000000000000000),
            (exactRationalLiteral (-2800868841508263) 6400000000000000000),
            (exactRationalLiteral (-177713979991037) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-26807991937210607) 1966080000000000000000),
            (exactRationalLiteral (13115311343984399) 51200000000000000000),
            (exactRationalLiteral (311058037223453) 800000000000000000),
            (exactRationalLiteral (13372206756967) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (26297207682477075461) 19660800000000000000000),
            (exactRationalLiteral (79296718454067511) 102400000000000000000),
            (exactRationalLiteral (175231825560413) 1600000000000000000),
            (exactRationalLiteral (-8847850306561) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (2947419458144997043) 78643200000000000000000),
            (exactRationalLiteral (1649397782415913) 16384000000000000000),
            (exactRationalLiteral (-428749454228357) 6400000000000000000),
            (exactRationalLiteral (-13259142011623) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6432476137232923753) 13107200000000000000000),
            (exactRationalLiteral (-756298800007769) 204800000000000000000),
            (exactRationalLiteral (1004561892354621) 3200000000000000000),
            (exactRationalLiteral (33203850923087) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-35131037976145852349) 78643200000000000000000),
            (exactRationalLiteral (-213870938041698639) 409600000000000000000),
            (exactRationalLiteral (-8647691926614389) 6400000000000000000),
            (exactRationalLiteral (-9613562530127) 12000000000000000)
          ],
          ![
            (exactRationalLiteral (-68484042813081447209) 78643200000000000000000),
            (exactRationalLiteral (131436269167975529) 81920000000000000000),
            (exactRationalLiteral (32156944746527359) 6400000000000000000),
            (exactRationalLiteral (850784696092613) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1161190426823669173) 1966080000000000000000),
            (exactRationalLiteral (-533296445228281619) 51200000000000000000),
            (exactRationalLiteral (-18407216711227361) 800000000000000000),
            (exactRationalLiteral (-6098604369457) 500000000000000)
          ],
          ![
            (exactRationalLiteral (-777723702740798368367) 78643200000000000000000),
            (exactRationalLiteral (2384868860952101231) 81920000000000000000),
            (exactRationalLiteral (559563048895028521) 6400000000000000000),
            (exactRationalLiteral (14530168493992243) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2264586789459729768733) 39321600000000000000000),
            (exactRationalLiteral (2772388255495149071) 204800000000000000000),
            (exactRationalLiteral (-540336828222984299) 3200000000000000000),
            (exactRationalLiteral (-17386370416405321) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1569410128811204415533) 26214400000000000000000),
            (exactRationalLiteral (-45000407686292558301) 409600000000000000000),
            (exactRationalLiteral (1004691169928695761) 6400000000000000000),
            (exactRationalLiteral (47194391250698347) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-27505500254840454247) 13107200000000000000000),
            (exactRationalLiteral (22589182988697396777) 204800000000000000000),
            (exactRationalLiteral (-188713784723813229) 3200000000000000000),
            (exactRationalLiteral (-6026843943221909) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (242297618812548370103) 15728640000000000000000),
            (exactRationalLiteral (-13289944102963333919) 409600000000000000000),
            (exactRationalLiteral (-3075549409798561) 1280000000000000000),
            (exactRationalLiteral (14659282055317369) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5390384888049635929) 78643200000000000000000),
            (exactRationalLiteral (-414644991388433533) 409600000000000000000),
            (exactRationalLiteral (31895768568341041) 6400000000000000000),
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
          (exactRationalLiteral (841557586072382851) 9830400000000000000000),
          (exactRationalLiteral (52137380577017898187) 3276800000000000000000),
          (exactRationalLiteral (6284671273039805293) 1638400000000000000000),
          (exactRationalLiteral (75627661587366470873) 1228800000000000000000),
          (exactRationalLiteral (11829508111307968009) 204800000000000000000),
          (exactRationalLiteral (33826357361537033063) 3276800000000000000000),
          (exactRationalLiteral (23317251610201819) 30720000000000000000),
          (exactRationalLiteral (1758999170026439767) 1966080000000000000000),
          (exactRationalLiteral (559356784454906947) 1228800000000000000000),
          (exactRationalLiteral (603100702382564273) 1228800000000000000000),
          (exactRationalLiteral (15988670751674447) 409600000000000000000),
          (exactRationalLiteral (414618979460400823) 307200000000000000000),
          (exactRationalLiteral (4311652295327321) 245760000000000000000),
          (exactRationalLiteral (10828687703289489521) 1228800000000000000000),
          (exactRationalLiteral (2066645883967314331) 409600000000000000000),
          (exactRationalLiteral (59177087282881196461) 9830400000000000000000),
          (exactRationalLiteral (33364367878621454391) 1638400000000000000000),
          (exactRationalLiteral (81242462679614138957) 1228800000000000000000),
          (exactRationalLiteral (495648546176584405661) 1228800000000000000000),
          (exactRationalLiteral (1070251093386680148227) 614400000000000000000),
          (exactRationalLiteral (57996696263978316089) 81920000000000000000),
          (exactRationalLiteral (4896444282673667024653) 2457600000000000000000),
          (exactRationalLiteral (219042144860052406883) 122880000000000000000),
          (exactRationalLiteral (8772358244904713533403) 4915200000000000000000),
          (exactRationalLiteral (6559700018063493422821) 2457600000000000000000),
          (exactRationalLiteral (8772358244904713533403) 4915200000000000000000),
          (exactRationalLiteral (219042144860052406883) 122880000000000000000),
          (exactRationalLiteral (4896444282673667024653) 2457600000000000000000),
          (exactRationalLiteral (57996696263978316089) 81920000000000000000),
          (exactRationalLiteral (1070251093386680148227) 614400000000000000000),
          (exactRationalLiteral (495648546176584405661) 1228800000000000000000),
          (exactRationalLiteral (81242462679614138957) 1228800000000000000000),
          (exactRationalLiteral (33364367878621454391) 1638400000000000000000),
          (exactRationalLiteral (59177087282881196461) 9830400000000000000000),
          (exactRationalLiteral (2066645883967314331) 409600000000000000000),
          (exactRationalLiteral (10828687703289489521) 1228800000000000000000),
          (exactRationalLiteral (4311652295327321) 245760000000000000000),
          (exactRationalLiteral (414618979460400823) 307200000000000000000),
          (exactRationalLiteral (15988670751674447) 409600000000000000000),
          (exactRationalLiteral (603100702382564273) 1228800000000000000000),
          (exactRationalLiteral (559356784454906947) 1228800000000000000000),
          (exactRationalLiteral (1758999170026439767) 1966080000000000000000),
          (exactRationalLiteral (23317251610201819) 30720000000000000000),
          (exactRationalLiteral (33826357361537033063) 3276800000000000000000),
          (exactRationalLiteral (11829508111307968009) 204800000000000000000),
          (exactRationalLiteral (75627661587366470873) 1228800000000000000000),
          (exactRationalLiteral (6284671273039805293) 1638400000000000000000),
          (exactRationalLiteral (52137380577017898187) 3276800000000000000000),
          (exactRationalLiteral (841557586072382851) 9830400000000000000000),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (18, 1),
      (17, 37),
      (17, 9),
      (16, 45),
      (16, 13),
      (15, 45),
      (15, 13),
      (14, 45),
      (14, 13),
      (13, 45),
      (13, 13),
      (12, 45),
      (12, 13),
      (11, 45),
      (11, 13),
      (10, 45),
      (10, 13),
      (9, 45),
      (9, 13),
      (8, 45),
      (8, 13),
      (7, 45),
      (7, 13),
      (6, 45),
      (6, 13),
      (5, 45),
      (5, 13),
      (4, 45),
      (4, 13),
      (3, 45),
      (3, 26),
      (3, 58),
      (4, 26),
      (4, 58),
      (5, 26),
      (5, 58),
      (6, 26),
      (6, 58),
      (7, 26),
      (7, 58),
      (8, 26),
      (8, 58),
      (9, 26),
      (9, 58),
      (10, 26),
      (10, 58),
      (11, 26),
      (11, 58),
      (12, 26),
      (12, 58),
      (13, 26),
      (13, 58),
      (14, 26)
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
theorem generatorCoordinates17_valid : ∀ i, (generatorCoordinates17 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
