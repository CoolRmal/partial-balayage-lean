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

/-- Actual coordinate interval candidates, block 20. -/
def generatorCoordinates20 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 4
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
            (exactRationalLiteral (3362198493513138241) 2457600000000000000000),
            (exactRationalLiteral (-197776381971361073) 25600000000000000000),
            (exactRationalLiteral (11633904821844769) 800000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (17588169470712152919) 655360000000000000000),
            (exactRationalLiteral (-346689680028542709) 20480000000000000000),
            (exactRationalLiteral (-35873937011107611) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-221345199169924593827) 4915200000000000000000),
            (exactRationalLiteral (6276738654109610531) 51200000000000000000),
            (exactRationalLiteral (104749555783517533) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-3061594469714578049) 204800000000000000000),
            (exactRationalLiteral (-1151858135314811871) 6400000000000000000),
            (exactRationalLiteral (720822620184513) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (225016258451408060051) 4915200000000000000000),
            (exactRationalLiteral (4949952190126650221) 51200000000000000000),
            (exactRationalLiteral (-19637702850017609) 320000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-73491413631116749429) 4915200000000000000000),
            (exactRationalLiteral (-151812690507705663) 10240000000000000000),
            (exactRationalLiteral (70714741113864683) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (135135737594747221) 81920000000000000000),
            (exactRationalLiteral (18013990482256333) 12800000000000000000),
            (exactRationalLiteral (-4910648336102037) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-12271518972475938161) 9830400000000000000000),
            (exactRationalLiteral (-86942991065433567) 102400000000000000000),
            (exactRationalLiteral (8078654300481583) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3903633844094884291) 9830400000000000000000),
            (exactRationalLiteral (-13926321822933) 4096000000000000000),
            (exactRationalLiteral (-2491881197633443) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (311154669019136347) 3276800000000000000000),
            (exactRationalLiteral (16907022617198399) 102400000000000000000),
            (exactRationalLiteral (963582928828017) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9215322527262125341) 4915200000000000000000),
            (exactRationalLiteral (8021567503332679) 10240000000000000000),
            (exactRationalLiteral (-210564124307) 2560000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (659492273025949291) 1638400000000000000000),
            (exactRationalLiteral (10321605630187283) 10240000000000000000),
            (exactRationalLiteral (906560209686273) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-22849257060772763641) 2457600000000000000000),
            (exactRationalLiteral (-6633856791457211) 5120000000000000000),
            (exactRationalLiteral (-725176131892153) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-15882456345199507367) 3276800000000000000000),
            (exactRationalLiteral (75742004191764869) 102400000000000000000),
            (exactRationalLiteral (1308439654512363) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-32711224387277981879) 9830400000000000000000),
            (exactRationalLiteral (449851720746237223) 102400000000000000000),
            (exactRationalLiteral (211975831673621) 640000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-31909212091509566063) 1966080000000000000000),
            (exactRationalLiteral (886667432072089467) 102400000000000000000),
            (exactRationalLiteral (7442915201788469) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-543851112587634044261) 9830400000000000000000),
            (exactRationalLiteral (2981392799368879989) 102400000000000000000),
            (exactRationalLiteral (8272870707860351) 640000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1214913090716175732023) 4915200000000000000000),
            (exactRationalLiteral (22494598410615079751) 51200000000000000000),
            (exactRationalLiteral (183224179071858601) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (51110267136398543647) 30720000000000000000),
            (exactRationalLiteral (-322672877081512021) 200000000000000000),
            (exactRationalLiteral (-62322748337698603) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-6756593643156456362123) 3276800000000000000000),
            (exactRationalLiteral (133437505103246627793) 102400000000000000000),
            (exactRationalLiteral (10263631043293151487) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1165515675923495319433) 1638400000000000000000),
            (exactRationalLiteral (3814479988267770993) 10240000000000000000),
            (exactRationalLiteral (-5624278914737078277) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (151138067701964712407) 2457600000000000000000),
            (exactRationalLiteral (-20244091494527969919) 25600000000000000000),
            (exactRationalLiteral (1462854101909422631) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-7283882032399979437661) 9830400000000000000000),
            (exactRationalLiteral (85664821850559423693) 102400000000000000000),
            (exactRationalLiteral (-2526740397788471357) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3445836918416389977203) 2457600000000000000000),
            (exactRationalLiteral (-6055055165344747271) 5120000000000000000),
            (exactRationalLiteral (616058841359073491) 800000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-7283882032399979437661) 9830400000000000000000),
            (exactRationalLiteral (85664821850559423693) 102400000000000000000),
            (exactRationalLiteral (-2526740397788471357) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (151138067701964712407) 2457600000000000000000),
            (exactRationalLiteral (-20244091494527969919) 25600000000000000000),
            (exactRationalLiteral (1462854101909422631) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1165515675923495319433) 1638400000000000000000),
            (exactRationalLiteral (3814479988267770993) 10240000000000000000),
            (exactRationalLiteral (-5624278914737078277) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6756593643156456362123) 3276800000000000000000),
            (exactRationalLiteral (133437505103246627793) 102400000000000000000),
            (exactRationalLiteral (10263631043293151487) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (51110267136398543647) 30720000000000000000),
            (exactRationalLiteral (-322672877081512021) 200000000000000000),
            (exactRationalLiteral (-62322748337698603) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-1214913090716175732023) 4915200000000000000000),
            (exactRationalLiteral (22494598410615079751) 51200000000000000000),
            (exactRationalLiteral (183224179071858601) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-543851112587634044261) 9830400000000000000000),
            (exactRationalLiteral (2981392799368879989) 102400000000000000000),
            (exactRationalLiteral (8272870707860351) 640000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-31909212091509566063) 1966080000000000000000),
            (exactRationalLiteral (886667432072089467) 102400000000000000000),
            (exactRationalLiteral (7442915201788469) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-32711224387277981879) 9830400000000000000000),
            (exactRationalLiteral (449851720746237223) 102400000000000000000),
            (exactRationalLiteral (211975831673621) 640000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-15882456345199507367) 3276800000000000000000),
            (exactRationalLiteral (75742004191764869) 102400000000000000000),
            (exactRationalLiteral (1308439654512363) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-22849257060772763641) 2457600000000000000000),
            (exactRationalLiteral (-6633856791457211) 5120000000000000000),
            (exactRationalLiteral (-725176131892153) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (659492273025949291) 1638400000000000000000),
            (exactRationalLiteral (10321605630187283) 10240000000000000000),
            (exactRationalLiteral (906560209686273) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (9215322527262125341) 4915200000000000000000),
            (exactRationalLiteral (8021567503332679) 10240000000000000000),
            (exactRationalLiteral (-210564124307) 2560000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (311154669019136347) 3276800000000000000000),
            (exactRationalLiteral (16907022617198399) 102400000000000000000),
            (exactRationalLiteral (963582928828017) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3903633844094884291) 9830400000000000000000),
            (exactRationalLiteral (-13926321822933) 4096000000000000000),
            (exactRationalLiteral (-2491881197633443) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-12271518972475938161) 9830400000000000000000),
            (exactRationalLiteral (-86942991065433567) 102400000000000000000),
            (exactRationalLiteral (8078654300481583) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (135135737594747221) 81920000000000000000),
            (exactRationalLiteral (18013990482256333) 12800000000000000000),
            (exactRationalLiteral (-4910648336102037) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-73491413631116749429) 4915200000000000000000),
            (exactRationalLiteral (-151812690507705663) 10240000000000000000),
            (exactRationalLiteral (70714741113864683) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (225016258451408060051) 4915200000000000000000),
            (exactRationalLiteral (4949952190126650221) 51200000000000000000),
            (exactRationalLiteral (-19637702850017609) 320000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3061594469714578049) 204800000000000000000),
            (exactRationalLiteral (-1151858135314811871) 6400000000000000000),
            (exactRationalLiteral (720822620184513) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-221345199169924593827) 4915200000000000000000),
            (exactRationalLiteral (6276738654109610531) 51200000000000000000),
            (exactRationalLiteral (104749555783517533) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (17588169470712152919) 655360000000000000000),
            (exactRationalLiteral (-346689680028542709) 20480000000000000000),
            (exactRationalLiteral (-35873937011107611) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (3362198493513138241) 2457600000000000000000),
            (exactRationalLiteral (-197776381971361073) 25600000000000000000),
            (exactRationalLiteral (11633904821844769) 800000000000000000),
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
          (exactRationalLiteral (166296404218134051) 102400000000000000000),
          (exactRationalLiteral (2237237378930946319) 81920000000000000000),
          (exactRationalLiteral (29980147433043997219) 614400000000000000000),
          (exactRationalLiteral (24677644779696197) 1200000000000000000),
          (exactRationalLiteral (14621126057379097) 300000000000000000),
          (exactRationalLiteral (6148152533788001) 400000000000000000),
          (exactRationalLiteral (201742054918273) 120000000000000000),
          (exactRationalLiteral (3053510986936637) 2400000000000000000),
          (exactRationalLiteral (955179647143873) 2400000000000000000),
          (exactRationalLiteral (241005883748557) 2400000000000000000),
          (exactRationalLiteral (284888868548251) 150000000000000000),
          (exactRationalLiteral (260744185621381) 600000000000000000),
          (exactRationalLiteral (2801629173973907) 300000000000000000),
          (exactRationalLiteral (1196763630231713513) 245760000000000000000),
          (exactRationalLiteral (283811994175671409) 81920000000000000000),
          (exactRationalLiteral (20272879096882958179) 1228800000000000000000),
          (exactRationalLiteral (69083516255031387197) 1228800000000000000000),
          (exactRationalLiteral (53408389495176195717) 204800000000000000000),
          (exactRationalLiteral (65775187544370700237) 38400000000000000000),
          (exactRationalLiteral (2579794904472404062633) 1228800000000000000000),
          (exactRationalLiteral (863601279450205741) 1200000000000000000),
          (exactRationalLiteral (9014626155573679537) 102400000000000000000),
          (exactRationalLiteral (943572102239547420101) 1228800000000000000000),
          (exactRationalLiteral (147438963604805878761) 102400000000000000000),
          (exactRationalLiteral (943572102239547420101) 1228800000000000000000),
          (exactRationalLiteral (9014626155573679537) 102400000000000000000),
          (exactRationalLiteral (863601279450205741) 1200000000000000000),
          (exactRationalLiteral (2579794904472404062633) 1228800000000000000000),
          (exactRationalLiteral (65775187544370700237) 38400000000000000000),
          (exactRationalLiteral (53408389495176195717) 204800000000000000000),
          (exactRationalLiteral (69083516255031387197) 1228800000000000000000),
          (exactRationalLiteral (20272879096882958179) 1228800000000000000000),
          (exactRationalLiteral (283811994175671409) 81920000000000000000),
          (exactRationalLiteral (1196763630231713513) 245760000000000000000),
          (exactRationalLiteral (2801629173973907) 300000000000000000),
          (exactRationalLiteral (260744185621381) 600000000000000000),
          (exactRationalLiteral (284888868548251) 150000000000000000),
          (exactRationalLiteral (241005883748557) 2400000000000000000),
          (exactRationalLiteral (955179647143873) 2400000000000000000),
          (exactRationalLiteral (3053510986936637) 2400000000000000000),
          (exactRationalLiteral (201742054918273) 120000000000000000),
          (exactRationalLiteral (6148152533788001) 400000000000000000),
          (exactRationalLiteral (14621126057379097) 300000000000000000),
          (exactRationalLiteral (24677644779696197) 1200000000000000000),
          (exactRationalLiteral (29980147433043997219) 614400000000000000000),
          (exactRationalLiteral (2237237378930946319) 81920000000000000000),
          (exactRationalLiteral (166296404218134051) 102400000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 56),
      (28, 8),
      (28, 24),
      (28, 40)
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
            (exactRationalLiteral (6159126082153113) 6553600000000000000),
            (exactRationalLiteral (-6159126082153113) 1024000000000000000),
            (exactRationalLiteral (2053042027384371) 160000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (16759983820866776777) 655360000000000000000),
            (exactRationalLiteral (-477151240688763573) 20480000000000000000),
            (exactRationalLiteral (-29356843319002821) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-182587668580271880797) 4915200000000000000000),
            (exactRationalLiteral (6615788875040100387) 51200000000000000000),
            (exactRationalLiteral (12955110936345479) 320000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-16061352589405084361) 614400000000000000000),
            (exactRationalLiteral (-1136009964741420391) 6400000000000000000),
            (exactRationalLiteral (7203262666511227) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (84461849393885978063) 1638400000000000000000),
            (exactRationalLiteral (4481117513371812717) 51200000000000000000),
            (exactRationalLiteral (-136228824127330707) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-77133526011351270827) 4915200000000000000000),
            (exactRationalLiteral (-88871753453586687) 10240000000000000000),
            (exactRationalLiteral (86637601521432757) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (414426528561815281) 245760000000000000000),
            (exactRationalLiteral (-3658394848374547) 12800000000000000000),
            (exactRationalLiteral (-5925544329213403) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-12688785225036128879) 9830400000000000000000),
            (exactRationalLiteral (-50904452750191391) 102400000000000000000),
            (exactRationalLiteral (1988122971427901) 640000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3937720349754319261) 9830400000000000000000),
            (exactRationalLiteral (-11363174343303949) 102400000000000000000),
            (exactRationalLiteral (-3015626951231869) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1047143347015345103) 9830400000000000000000),
            (exactRationalLiteral (21098458886915199) 102400000000000000000),
            (exactRationalLiteral (1132135206030383) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3151429340503398049) 1638400000000000000000),
            (exactRationalLiteral (39530277246091363) 51200000000000000000),
            (exactRationalLiteral (-157177557594141) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2298969986104799359) 4915200000000000000000),
            (exactRationalLiteral (55217406792230367) 51200000000000000000),
            (exactRationalLiteral (898129110960703) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-23057020895330768839) 2457600000000000000000),
            (exactRationalLiteral (-36092997100646183) 25600000000000000000),
            (exactRationalLiteral (-736680439787911) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-47178211894127697323) 9830400000000000000000),
            (exactRationalLiteral (3219107321714317) 4096000000000000000),
            (exactRationalLiteral (211879954206833) 640000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2000045360039220167) 655360000000000000000),
            (exactRationalLiteral (453448793535629031) 102400000000000000000),
            (exactRationalLiteral (738657236327799) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-154142350747454374901) 9830400000000000000000),
            (exactRationalLiteral (182726832099794367) 20480000000000000000),
            (exactRationalLiteral (1208089802330543) 640000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-525490926627922594363) 9830400000000000000000),
            (exactRationalLiteral (3134578674039361461) 102400000000000000000),
            (exactRationalLiteral (35228583795938981) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-14374849790883153819) 65536000000000000000),
            (exactRationalLiteral (4608806604119144219) 10240000000000000000),
            (exactRationalLiteral (91493125918462071) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (239377295077652637847) 153600000000000000000),
            (exactRationalLiteral (-699902193047612663) 400000000000000000),
            (exactRationalLiteral (-46790129431478639) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-19353538853290347615551) 9830400000000000000000),
            (exactRationalLiteral (170718765796431176849) 102400000000000000000),
            (exactRationalLiteral (8376999303299123041) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3546845678663685562949) 4915200000000000000000),
            (exactRationalLiteral (-1746916606603751051) 51200000000000000000),
            (exactRationalLiteral (-4785379359234224731) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (15496927339259537939) 819200000000000000000),
            (exactRationalLiteral (-14761168056855954719) 25600000000000000000),
            (exactRationalLiteral (1278607616926584969) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-6799253195899234647811) 9830400000000000000000),
            (exactRationalLiteral (76038255344830490253) 102400000000000000000),
            (exactRationalLiteral (-2286542855075995363) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1090461445598244990927) 819200000000000000000),
            (exactRationalLiteral (-27907856840098176483) 25600000000000000000),
            (exactRationalLiteral (113530130390741289) 160000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-6799253195899234647811) 9830400000000000000000),
            (exactRationalLiteral (76038255344830490253) 102400000000000000000),
            (exactRationalLiteral (-2286542855075995363) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (15496927339259537939) 819200000000000000000),
            (exactRationalLiteral (-14761168056855954719) 25600000000000000000),
            (exactRationalLiteral (1278607616926584969) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (3546845678663685562949) 4915200000000000000000),
            (exactRationalLiteral (-1746916606603751051) 51200000000000000000),
            (exactRationalLiteral (-4785379359234224731) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-19353538853290347615551) 9830400000000000000000),
            (exactRationalLiteral (170718765796431176849) 102400000000000000000),
            (exactRationalLiteral (8376999303299123041) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (239377295077652637847) 153600000000000000000),
            (exactRationalLiteral (-699902193047612663) 400000000000000000),
            (exactRationalLiteral (-46790129431478639) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-14374849790883153819) 65536000000000000000),
            (exactRationalLiteral (4608806604119144219) 10240000000000000000),
            (exactRationalLiteral (91493125918462071) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-525490926627922594363) 9830400000000000000000),
            (exactRationalLiteral (3134578674039361461) 102400000000000000000),
            (exactRationalLiteral (35228583795938981) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-154142350747454374901) 9830400000000000000000),
            (exactRationalLiteral (182726832099794367) 20480000000000000000),
            (exactRationalLiteral (1208089802330543) 640000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2000045360039220167) 655360000000000000000),
            (exactRationalLiteral (453448793535629031) 102400000000000000000),
            (exactRationalLiteral (738657236327799) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-47178211894127697323) 9830400000000000000000),
            (exactRationalLiteral (3219107321714317) 4096000000000000000),
            (exactRationalLiteral (211879954206833) 640000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-23057020895330768839) 2457600000000000000000),
            (exactRationalLiteral (-36092997100646183) 25600000000000000000),
            (exactRationalLiteral (-736680439787911) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (2298969986104799359) 4915200000000000000000),
            (exactRationalLiteral (55217406792230367) 51200000000000000000),
            (exactRationalLiteral (898129110960703) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (3151429340503398049) 1638400000000000000000),
            (exactRationalLiteral (39530277246091363) 51200000000000000000),
            (exactRationalLiteral (-157177557594141) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1047143347015345103) 9830400000000000000000),
            (exactRationalLiteral (21098458886915199) 102400000000000000000),
            (exactRationalLiteral (1132135206030383) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3937720349754319261) 9830400000000000000000),
            (exactRationalLiteral (-11363174343303949) 102400000000000000000),
            (exactRationalLiteral (-3015626951231869) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-12688785225036128879) 9830400000000000000000),
            (exactRationalLiteral (-50904452750191391) 102400000000000000000),
            (exactRationalLiteral (1988122971427901) 640000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (414426528561815281) 245760000000000000000),
            (exactRationalLiteral (-3658394848374547) 12800000000000000000),
            (exactRationalLiteral (-5925544329213403) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-77133526011351270827) 4915200000000000000000),
            (exactRationalLiteral (-88871753453586687) 10240000000000000000),
            (exactRationalLiteral (86637601521432757) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (84461849393885978063) 1638400000000000000000),
            (exactRationalLiteral (4481117513371812717) 51200000000000000000),
            (exactRationalLiteral (-136228824127330707) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-16061352589405084361) 614400000000000000000),
            (exactRationalLiteral (-1136009964741420391) 6400000000000000000),
            (exactRationalLiteral (7203262666511227) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-182587668580271880797) 4915200000000000000000),
            (exactRationalLiteral (6615788875040100387) 51200000000000000000),
            (exactRationalLiteral (12955110936345479) 320000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (16759983820866776777) 655360000000000000000),
            (exactRationalLiteral (-477151240688763573) 20480000000000000000),
            (exactRationalLiteral (-29356843319002821) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (6159126082153113) 6553600000000000000),
            (exactRationalLiteral (-6159126082153113) 1024000000000000000),
            (exactRationalLiteral (2053042027384371) 160000000000000000),
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
          (exactRationalLiteral (405094405741805177) 12800000000000000000),
          (exactRationalLiteral (33300149261806594861) 614400000000000000000),
          (exactRationalLiteral (9774841009798373603) 614400000000000000000),
          (exactRationalLiteral (4064861589824431) 2400000000000000000),
          (exactRationalLiteral (1601343219804619447) 1228800000000000000000),
          (exactRationalLiteral (497639828314340741) 1228800000000000000000),
          (exactRationalLiteral (46413308559699293) 409600000000000000000),
          (exactRationalLiteral (239309863327143367) 122880000000000000000),
          (exactRationalLiteral (102804682427708741) 204800000000000000000),
          (exactRationalLiteral (23167515680106019) 2457600000000000000),
          (exactRationalLiteral (11576255425781599) 2400000000000000000),
          (exactRationalLiteral (7655920458624313) 2400000000000000000),
          (exactRationalLiteral (12765660046290793) 800000000000000000),
          (exactRationalLiteral (43520988689272557) 800000000000000000),
          (exactRationalLiteral (280011105584397367) 1200000000000000000),
          (exactRationalLiteral (322432271740203703) 200000000000000000),
          (exactRationalLiteral (4843657430883727237) 2400000000000000000),
          (exactRationalLiteral (2313670198181819639) 3200000000000000000),
          (exactRationalLiteral (46241324356258619) 1200000000000000000),
          (exactRationalLiteral (572456680441919787) 800000000000000000),
          (exactRationalLiteral (819539810391990553) 600000000000000000),
          (exactRationalLiteral (572456680441919787) 800000000000000000),
          (exactRationalLiteral (46241324356258619) 1200000000000000000),
          (exactRationalLiteral (2313670198181819639) 3200000000000000000),
          (exactRationalLiteral (4843657430883727237) 2400000000000000000),
          (exactRationalLiteral (322432271740203703) 200000000000000000),
          (exactRationalLiteral (280011105584397367) 1200000000000000000),
          (exactRationalLiteral (43520988689272557) 800000000000000000),
          (exactRationalLiteral (12765660046290793) 800000000000000000),
          (exactRationalLiteral (7655920458624313) 2400000000000000000),
          (exactRationalLiteral (11576255425781599) 2400000000000000000),
          (exactRationalLiteral (23167515680106019) 2457600000000000000),
          (exactRationalLiteral (102804682427708741) 204800000000000000000),
          (exactRationalLiteral (239309863327143367) 122880000000000000000),
          (exactRationalLiteral (46413308559699293) 409600000000000000000),
          (exactRationalLiteral (497639828314340741) 1228800000000000000000),
          (exactRationalLiteral (1601343219804619447) 1228800000000000000000),
          (exactRationalLiteral (4064861589824431) 2400000000000000000),
          (exactRationalLiteral (9774841009798373603) 614400000000000000000),
          (exactRationalLiteral (33300149261806594861) 614400000000000000000),
          (exactRationalLiteral (405094405741805177) 12800000000000000000),
          (exactRationalLiteral (12342573336230231) 300000000000000000),
          (exactRationalLiteral (4200852547840459) 160000000000000000),
          (exactRationalLiteral (684347342461457) 600000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 55),
      (28, 7),
      (28, 23),
      (28, 39)
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
            (exactRationalLiteral (1503511111387821029) 2457600000000000000000),
            (exactRationalLiteral (-115654700875986233) 25600000000000000000),
            (exactRationalLiteral (8896515451998941) 800000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (15696943424469378067) 655360000000000000000),
            (exactRationalLiteral (-581544426580565277) 20480000000000000000),
            (exactRationalLiteral (-22839749626898031) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-142275524678257710287) 4915200000000000000000),
            (exactRationalLiteral (6794943091563429691) 51200000000000000000),
            (exactRationalLiteral (24801553579937257) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-22765043465670165127) 614400000000000000000),
            (exactRationalLiteral (-218846406796544411) 1280000000000000000),
            (exactRationalLiteral (13685702712837941) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (278485346132851871359) 4915200000000000000000),
            (exactRationalLiteral (772024319421600913) 10240000000000000000),
            (exactRationalLiteral (-174269134004573369) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-26232111985023802019) 1638400000000000000000),
            (exactRationalLiteral (-65962640367066259) 51200000000000000000),
            (exactRationalLiteral (102560461929000831) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1975016157795822823) 1228800000000000000000),
            (exactRationalLiteral (-29390364151450891) 12800000000000000000),
            (exactRationalLiteral (-6940440322324769) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-12867476721024971477) 9830400000000000000000),
            (exactRationalLiteral (-7418072208317527) 102400000000000000000),
            (exactRationalLiteral (11802575413797427) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-4044181902243319087) 9830400000000000000000),
            (exactRationalLiteral (-24473173655428277) 102400000000000000000),
            (exactRationalLiteral (-707874540966059) 640000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1187993931918010357) 9830400000000000000000),
            (exactRationalLiteral (25964104265441463) 102400000000000000000),
            (exactRationalLiteral (1300687483232749) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9689481254376003569) 4915200000000000000000),
            (exactRationalLiteral (38850417055910267) 51200000000000000000),
            (exactRationalLiteral (-182752537496407) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2641018251794807717) 4915200000000000000000),
            (exactRationalLiteral (58793061038622039) 51200000000000000000),
            (exactRationalLiteral (889698012235133) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-23282465060443683901) 2457600000000000000000),
            (exactRationalLiteral (-39062727475589343) 25600000000000000000),
            (exactRationalLiteral (-748184747683669) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-9336725831630410517) 1966080000000000000000),
            (exactRationalLiteral (84217202360038189) 102400000000000000000),
            (exactRationalLiteral (810359887555967) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5454481728045351191) 1966080000000000000000),
            (exactRationalLiteral (91152195727371923) 20480000000000000000),
            (exactRationalLiteral (417435314287493) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-49531223420360418109) 3276800000000000000000),
            (exactRationalLiteral (934991024165311187) 102400000000000000000),
            (exactRationalLiteral (4637982821516961) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-168761751552369536307) 3276800000000000000000),
            (exactRationalLiteral (3263221469736391837) 102400000000000000000),
            (exactRationalLiteral (29092814052576207) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-939118542894254251123) 4915200000000000000000),
            (exactRationalLiteral (23226543417962776319) 51200000000000000000),
            (exactRationalLiteral (-237927234934459) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (74026763788985690041) 51200000000000000000),
            (exactRationalLiteral (-18473150325649533) 10000000000000000),
            (exactRationalLiteral (-1250300421010347) 2000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-18236248793832147191749) 9830400000000000000000),
            (exactRationalLiteral (200453499529639612121) 102400000000000000000),
            (exactRationalLiteral (1298073512661018919) 640000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (696459044987052754811) 983040000000000000000),
            (exactRationalLiteral (-19210634932534942883) 51200000000000000000),
            (exactRationalLiteral (-789295960746274237) 320000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-27469920860169445517) 2457600000000000000000),
            (exactRationalLiteral (-10015230559115290167) 25600000000000000000),
            (exactRationalLiteral (1094361131943747307) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2123167129306771248891) 3276800000000000000000),
            (exactRationalLiteral (67372479009951460789) 102400000000000000000),
            (exactRationalLiteral (-2046345312363519369) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3110555370819968923039) 2457600000000000000000),
            (exactRationalLiteral (-5146814122218816959) 5120000000000000000),
            (exactRationalLiteral (519242462548339399) 800000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2123167129306771248891) 3276800000000000000000),
            (exactRationalLiteral (67372479009951460789) 102400000000000000000),
            (exactRationalLiteral (-2046345312363519369) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-27469920860169445517) 2457600000000000000000),
            (exactRationalLiteral (-10015230559115290167) 25600000000000000000),
            (exactRationalLiteral (1094361131943747307) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (696459044987052754811) 983040000000000000000),
            (exactRationalLiteral (-19210634932534942883) 51200000000000000000),
            (exactRationalLiteral (-789295960746274237) 320000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-18236248793832147191749) 9830400000000000000000),
            (exactRationalLiteral (200453499529639612121) 102400000000000000000),
            (exactRationalLiteral (1298073512661018919) 640000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (74026763788985690041) 51200000000000000000),
            (exactRationalLiteral (-18473150325649533) 10000000000000000),
            (exactRationalLiteral (-1250300421010347) 2000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-939118542894254251123) 4915200000000000000000),
            (exactRationalLiteral (23226543417962776319) 51200000000000000000),
            (exactRationalLiteral (-237927234934459) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-168761751552369536307) 3276800000000000000000),
            (exactRationalLiteral (3263221469736391837) 102400000000000000000),
            (exactRationalLiteral (29092814052576207) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-49531223420360418109) 3276800000000000000000),
            (exactRationalLiteral (934991024165311187) 102400000000000000000),
            (exactRationalLiteral (4637982821516961) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5454481728045351191) 1966080000000000000000),
            (exactRationalLiteral (91152195727371923) 20480000000000000000),
            (exactRationalLiteral (417435314287493) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9336725831630410517) 1966080000000000000000),
            (exactRationalLiteral (84217202360038189) 102400000000000000000),
            (exactRationalLiteral (810359887555967) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-23282465060443683901) 2457600000000000000000),
            (exactRationalLiteral (-39062727475589343) 25600000000000000000),
            (exactRationalLiteral (-748184747683669) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (2641018251794807717) 4915200000000000000000),
            (exactRationalLiteral (58793061038622039) 51200000000000000000),
            (exactRationalLiteral (889698012235133) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (9689481254376003569) 4915200000000000000000),
            (exactRationalLiteral (38850417055910267) 51200000000000000000),
            (exactRationalLiteral (-182752537496407) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1187993931918010357) 9830400000000000000000),
            (exactRationalLiteral (25964104265441463) 102400000000000000000),
            (exactRationalLiteral (1300687483232749) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4044181902243319087) 9830400000000000000000),
            (exactRationalLiteral (-24473173655428277) 102400000000000000000),
            (exactRationalLiteral (-707874540966059) 640000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-12867476721024971477) 9830400000000000000000),
            (exactRationalLiteral (-7418072208317527) 102400000000000000000),
            (exactRationalLiteral (11802575413797427) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1975016157795822823) 1228800000000000000000),
            (exactRationalLiteral (-29390364151450891) 12800000000000000000),
            (exactRationalLiteral (-6940440322324769) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-26232111985023802019) 1638400000000000000000),
            (exactRationalLiteral (-65962640367066259) 51200000000000000000),
            (exactRationalLiteral (102560461929000831) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (278485346132851871359) 4915200000000000000000),
            (exactRationalLiteral (772024319421600913) 10240000000000000000),
            (exactRationalLiteral (-174269134004573369) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-22765043465670165127) 614400000000000000000),
            (exactRationalLiteral (-218846406796544411) 1280000000000000000),
            (exactRationalLiteral (13685702712837941) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-142275524678257710287) 4915200000000000000000),
            (exactRationalLiteral (6794943091563429691) 51200000000000000000),
            (exactRationalLiteral (24801553579937257) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (15696943424469378067) 655360000000000000000),
            (exactRationalLiteral (-581544426580565277) 20480000000000000000),
            (exactRationalLiteral (-22839749626898031) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (1503511111387821029) 2457600000000000000000),
            (exactRationalLiteral (-115654700875986233) 25600000000000000000),
            (exactRationalLiteral (8896515451998941) 800000000000000000),
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
          (exactRationalLiteral (234731138464279751) 307200000000000000000),
          (exactRationalLiteral (2031820239892628481) 81920000000000000000),
          (exactRationalLiteral (4064149057291432313) 122880000000000000000),
          (exactRationalLiteral (812607538733020441) 19200000000000000000),
          (exactRationalLiteral (1507936892537622623) 25600000000000000000),
          (exactRationalLiteral (2464775640236601787) 153600000000000000000),
          (exactRationalLiteral (85119724053323203) 51200000000000000000),
          (exactRationalLiteral (402738385903919231) 307200000000000000000),
          (exactRationalLiteral (64507522096888969) 153600000000000000000),
          (exactRationalLiteral (19841759114103659) 153600000000000000000),
          (exactRationalLiteral (51070163856465073) 25600000000000000000),
          (exactRationalLiteral (44063473646844007) 76800000000000000000),
          (exactRationalLiteral (365654742957303919) 38400000000000000000),
          (exactRationalLiteral (1955571881901156673) 409600000000000000000),
          (exactRationalLiteral (3579784832404181521) 1228800000000000000000),
          (exactRationalLiteral (18923003519002196141) 1228800000000000000000),
          (exactRationalLiteral (64498071592411046803) 1228800000000000000000),
          (exactRationalLiteral (126094127675408835649) 614400000000000000000),
          (exactRationalLiteral (57711466170559989989) 38400000000000000000),
          (exactRationalLiteral (784049786410881405421) 409600000000000000000),
          (exactRationalLiteral (146986176689330127599) 204800000000000000000),
          (exactRationalLiteral (282940897834247359) 12800000000000000000),
          (exactRationalLiteral (822234744957326865643) 1228800000000000000000),
          (exactRationalLiteral (398667439266949859893) 307200000000000000000),
          (exactRationalLiteral (822234744957326865643) 1228800000000000000000),
          (exactRationalLiteral (282940897834247359) 12800000000000000000),
          (exactRationalLiteral (146986176689330127599) 204800000000000000000),
          (exactRationalLiteral (784049786410881405421) 409600000000000000000),
          (exactRationalLiteral (57711466170559989989) 38400000000000000000),
          (exactRationalLiteral (126094127675408835649) 614400000000000000000),
          (exactRationalLiteral (64498071592411046803) 1228800000000000000000),
          (exactRationalLiteral (18923003519002196141) 1228800000000000000000),
          (exactRationalLiteral (3579784832404181521) 1228800000000000000000),
          (exactRationalLiteral (1955571881901156673) 409600000000000000000),
          (exactRationalLiteral (365654742957303919) 38400000000000000000),
          (exactRationalLiteral (44063473646844007) 76800000000000000000),
          (exactRationalLiteral (51070163856465073) 25600000000000000000),
          (exactRationalLiteral (19841759114103659) 153600000000000000000),
          (exactRationalLiteral (64507522096888969) 153600000000000000000),
          (exactRationalLiteral (402738385903919231) 307200000000000000000),
          (exactRationalLiteral (85119724053323203) 51200000000000000000),
          (exactRationalLiteral (2464775640236601787) 153600000000000000000),
          (exactRationalLiteral (1507936892537622623) 25600000000000000000),
          (exactRationalLiteral (812607538733020441) 19200000000000000000),
          (exactRationalLiteral (4064149057291432313) 122880000000000000000),
          (exactRationalLiteral (2031820239892628481) 81920000000000000000),
          (exactRationalLiteral (234731138464279751) 307200000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 54),
      (28, 6),
      (28, 22),
      (28, 38)
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
            (exactRationalLiteral (910866312816199267) 2457600000000000000000),
            (exactRationalLiteral (-82806028437836297) 25600000000000000000),
            (exactRationalLiteral (7527820767076027) 800000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (14451185031056795109) 655360000000000000000),
            (exactRationalLiteral (-659869237703947821) 20480000000000000000),
            (exactRationalLiteral (-16322655934793241) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-101368143490325045609) 4915200000000000000000),
            (exactRationalLiteral (6814201303679598443) 51200000000000000000),
            (exactRationalLiteral (-15172447521852881) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-9713425825609045103) 204800000000000000000),
            (exactRationalLiteral (-1026524343038716863) 6400000000000000000),
            (exactRationalLiteral (4033628551832931) 40000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (299402684867936047673) 4915200000000000000000),
            (exactRationalLiteral (617392888267045153) 10240000000000000000),
            (exactRationalLiteral (-212309443881816031) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-77797694812495521343) 4915200000000000000000),
            (exactRationalLiteral (376124928164073213) 51200000000000000000),
            (exactRationalLiteral (23696664467313781) 320000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (114088607003118319) 81920000000000000000),
            (exactRationalLiteral (-59181917426972699) 12800000000000000000),
            (exactRationalLiteral (-1591067263087227) 80000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-12762906407082675827) 9830400000000000000000),
            (exactRationalLiteral (1740646022407521) 4096000000000000000),
            (exactRationalLiteral (13664535970455349) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-4235588399648245993) 9830400000000000000000),
            (exactRationalLiteral (-39678155981946309) 102400000000000000000),
            (exactRationalLiteral (-4063118458428721) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (453353672139420529) 3276800000000000000000),
            (exactRationalLiteral (31503958752777191) 102400000000000000000),
            (exactRationalLiteral (293847952087023) 640000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9920288426341899223) 4915200000000000000000),
            (exactRationalLiteral (38068256946120107) 51200000000000000000),
            (exactRationalLiteral (-208327517398673) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1001473089926153089) 1638400000000000000000),
            (exactRationalLiteral (62334990890111431) 51200000000000000000),
            (exactRationalLiteral (881266913509563) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-23525865659501007019) 2457600000000000000000),
            (exactRationalLiteral (-8415695016423107) 5120000000000000000),
            (exactRationalLiteral (-759689055579427) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-15389865928291688213) 3276800000000000000000),
            (exactRationalLiteral (86960562143305661) 102400000000000000000),
            (exactRationalLiteral (561320004077769) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-24534118432322309573) 9830400000000000000000),
            (exactRationalLiteral (18271531041997159) 4096000000000000000),
            (exactRationalLiteral (96213392247187) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-142933678186991726689) 9830400000000000000000),
            (exactRationalLiteral (950738023071107523) 102400000000000000000),
            (exactRationalLiteral (3235516631381207) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-486381355149032794511) 9830400000000000000000),
            (exactRationalLiteral (3367321186459971117) 102400000000000000000),
            (exactRationalLiteral (22957044309213433) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-800129061725910392837) 4915200000000000000000),
            (exactRationalLiteral (23042129602716245423) 51200000000000000000),
            (exactRationalLiteral (-91968980388330989) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (204033107403655294199) 153600000000000000000),
            (exactRationalLiteral (-762417214098130013) 400000000000000000),
            (exactRationalLiteral (-15724891619038711) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-5654396637618208165889) 3276800000000000000000),
            (exactRationalLiteral (222641706302871933609) 102400000000000000000),
            (exactRationalLiteral (4603735823311066149) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1107676418639096358907) 1638400000000000000000),
            (exactRationalLiteral (-33318755036454720531) 51200000000000000000),
            (exactRationalLiteral (-3107580248228517639) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-75165956571467569483) 2457600000000000000000),
            (exactRationalLiteral (-6006279001305976263) 25600000000000000000),
            (exactRationalLiteral (182022929392181929) 160000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-5988861867438117310391) 9830400000000000000000),
            (exactRationalLiteral (59667492845922335301) 102400000000000000000),
            (exactRationalLiteral (-14449182157208347) 25600000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2962188223946363018873) 2457600000000000000000),
            (exactRationalLiteral (-23753917139711461291) 25600000000000000000),
            (exactRationalLiteral (470834273142972353) 800000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-5988861867438117310391) 9830400000000000000000),
            (exactRationalLiteral (59667492845922335301) 102400000000000000000),
            (exactRationalLiteral (-14449182157208347) 25600000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-75165956571467569483) 2457600000000000000000),
            (exactRationalLiteral (-6006279001305976263) 25600000000000000000),
            (exactRationalLiteral (182022929392181929) 160000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1107676418639096358907) 1638400000000000000000),
            (exactRationalLiteral (-33318755036454720531) 51200000000000000000),
            (exactRationalLiteral (-3107580248228517639) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5654396637618208165889) 3276800000000000000000),
            (exactRationalLiteral (222641706302871933609) 102400000000000000000),
            (exactRationalLiteral (4603735823311066149) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (204033107403655294199) 153600000000000000000),
            (exactRationalLiteral (-762417214098130013) 400000000000000000),
            (exactRationalLiteral (-15724891619038711) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-800129061725910392837) 4915200000000000000000),
            (exactRationalLiteral (23042129602716245423) 51200000000000000000),
            (exactRationalLiteral (-91968980388330989) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-486381355149032794511) 9830400000000000000000),
            (exactRationalLiteral (3367321186459971117) 102400000000000000000),
            (exactRationalLiteral (22957044309213433) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-142933678186991726689) 9830400000000000000000),
            (exactRationalLiteral (950738023071107523) 102400000000000000000),
            (exactRationalLiteral (3235516631381207) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-24534118432322309573) 9830400000000000000000),
            (exactRationalLiteral (18271531041997159) 4096000000000000000),
            (exactRationalLiteral (96213392247187) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-15389865928291688213) 3276800000000000000000),
            (exactRationalLiteral (86960562143305661) 102400000000000000000),
            (exactRationalLiteral (561320004077769) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-23525865659501007019) 2457600000000000000000),
            (exactRationalLiteral (-8415695016423107) 5120000000000000000),
            (exactRationalLiteral (-759689055579427) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (1001473089926153089) 1638400000000000000000),
            (exactRationalLiteral (62334990890111431) 51200000000000000000),
            (exactRationalLiteral (881266913509563) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (9920288426341899223) 4915200000000000000000),
            (exactRationalLiteral (38068256946120107) 51200000000000000000),
            (exactRationalLiteral (-208327517398673) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (453353672139420529) 3276800000000000000000),
            (exactRationalLiteral (31503958752777191) 102400000000000000000),
            (exactRationalLiteral (293847952087023) 640000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4235588399648245993) 9830400000000000000000),
            (exactRationalLiteral (-39678155981946309) 102400000000000000000),
            (exactRationalLiteral (-4063118458428721) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-12762906407082675827) 9830400000000000000000),
            (exactRationalLiteral (1740646022407521) 4096000000000000000),
            (exactRationalLiteral (13664535970455349) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (114088607003118319) 81920000000000000000),
            (exactRationalLiteral (-59181917426972699) 12800000000000000000),
            (exactRationalLiteral (-1591067263087227) 80000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-77797694812495521343) 4915200000000000000000),
            (exactRationalLiteral (376124928164073213) 51200000000000000000),
            (exactRationalLiteral (23696664467313781) 320000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (299402684867936047673) 4915200000000000000000),
            (exactRationalLiteral (617392888267045153) 10240000000000000000),
            (exactRationalLiteral (-212309443881816031) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-9713425825609045103) 204800000000000000000),
            (exactRationalLiteral (-1026524343038716863) 6400000000000000000),
            (exactRationalLiteral (4033628551832931) 40000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-101368143490325045609) 4915200000000000000000),
            (exactRationalLiteral (6814201303679598443) 51200000000000000000),
            (exactRationalLiteral (-15172447521852881) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (14451185031056795109) 655360000000000000000),
            (exactRationalLiteral (-659869237703947821) 20480000000000000000),
            (exactRationalLiteral (-16322655934793241) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (910866312816199267) 2457600000000000000000),
            (exactRationalLiteral (-82806028437836297) 25600000000000000000),
            (exactRationalLiteral (7527820767076027) 800000000000000000),
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
          (exactRationalLiteral (1004878276801332143) 19200000000000000000),
          (exactRationalLiteral (38500953713169706943) 614400000000000000000),
          (exactRationalLiteral (1227790329065340911) 76800000000000000000),
          (exactRationalLiteral (5829738426181063) 3840000000000000000),
          (exactRationalLiteral (200834253611409419) 153600000000000000000),
          (exactRationalLiteral (545884261980771287) 1228800000000000000000),
          (exactRationalLiteral (182383111012062461) 1228800000000000000000),
          (exactRationalLiteral (1254231928392264049) 614400000000000000000),
          (exactRationalLiteral (399257978454994933) 614400000000000000000),
          (exactRationalLiteral (2956798238008504973) 307200000000000000000),
          (exactRationalLiteral (725447984239859519) 153600000000000000000),
          (exactRationalLiteral (134916843798616327) 51200000000000000000),
          (exactRationalLiteral (455548388978799493) 30720000000000000000),
          (exactRationalLiteral (7756427807665834159) 153600000000000000000),
          (exactRationalLiteral (4528570270565871999) 25600000000000000000),
          (exactRationalLiteral (2664089662356532853) 1920000000000000000),
          (exactRationalLiteral (275255632944114220091) 153600000000000000000),
          (exactRationalLiteral (53331927039128379041) 76800000000000000000),
          (exactRationalLiteral (11318321609624273521) 307200000000000000000),
          (exactRationalLiteral (96459420125878026319) 153600000000000000000),
          (exactRationalLiteral (15806701470206401059) 12800000000000000000),
          (exactRationalLiteral (96459420125878026319) 153600000000000000000),
          (exactRationalLiteral (11318321609624273521) 307200000000000000000),
          (exactRationalLiteral (53331927039128379041) 76800000000000000000),
          (exactRationalLiteral (275255632944114220091) 153600000000000000000),
          (exactRationalLiteral (2664089662356532853) 1920000000000000000),
          (exactRationalLiteral (4528570270565871999) 25600000000000000000),
          (exactRationalLiteral (7756427807665834159) 153600000000000000000),
          (exactRationalLiteral (455548388978799493) 30720000000000000000),
          (exactRationalLiteral (134916843798616327) 51200000000000000000),
          (exactRationalLiteral (725447984239859519) 153600000000000000000),
          (exactRationalLiteral (2956798238008504973) 307200000000000000000),
          (exactRationalLiteral (399257978454994933) 614400000000000000000),
          (exactRationalLiteral (1254231928392264049) 614400000000000000000),
          (exactRationalLiteral (182383111012062461) 1228800000000000000000),
          (exactRationalLiteral (545884261980771287) 1228800000000000000000),
          (exactRationalLiteral (200834253611409419) 153600000000000000000),
          (exactRationalLiteral (5829738426181063) 3840000000000000000),
          (exactRationalLiteral (1227790329065340911) 76800000000000000000),
          (exactRationalLiteral (38500953713169706943) 614400000000000000000),
          (exactRationalLiteral (1004878276801332143) 19200000000000000000),
          (exactRationalLiteral (1903691839740289133) 76800000000000000000),
          (exactRationalLiteral (235838209852248941) 10240000000000000000),
          (exactRationalLiteral (6159126082153113) 12800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 53),
      (28, 5),
      (28, 21),
      (28, 37)
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
            (exactRationalLiteral (166296404218134051) 819200000000000000000),
            (exactRationalLiteral (-55432134739378017) 25600000000000000000),
            (exactRationalLiteral (6159126082153113) 800000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (13074845390165866223) 655360000000000000000),
            (exactRationalLiteral (-142425134811782241) 4096000000000000000),
            (exactRationalLiteral (-9805562242688451) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-2432996041716674003) 196608000000000000000),
            (exactRationalLiteral (6673563511388606643) 51200000000000000000),
            (exactRationalLiteral (-55146448623643019) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-35031476061764153771) 614400000000000000000),
            (exactRationalLiteral (-186577378381880963) 1280000000000000000),
            (exactRationalLiteral (26650582805491369) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (105074865649952213081) 1638400000000000000000),
            (exactRationalLiteral (2161646046053476317) 51200000000000000000),
            (exactRationalLiteral (-250349753759058693) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-74055453933841982909) 4915200000000000000000),
            (exactRationalLiteral (881903938325484981) 51200000000000000000),
            (exactRationalLiteral (134406182744136979) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1256713980727259507) 1228800000000000000000),
            (exactRationalLiteral (-93033054674939971) 12800000000000000000),
            (exactRationalLiteral (-8970232308547501) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-12330387229849451801) 9830400000000000000000),
            (exactRationalLiteral (20379643111065053) 20480000000000000000),
            (exactRationalLiteral (15526496527113271) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-4524509740055462203) 9830400000000000000000),
            (exactRationalLiteral (-11395624264571609) 20480000000000000000),
            (exactRationalLiteral (-4586864212027147) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1567389855168955577) 9830400000000000000000),
            (exactRationalLiteral (37718022348922383) 102400000000000000000),
            (exactRationalLiteral (1637792037637481) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (135281276505203023) 65536000000000000000),
            (exactRationalLiteral (37183796916720883) 51200000000000000000),
            (exactRationalLiteral (-233902497300939) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3388970693686340329) 4915200000000000000000),
            (exactRationalLiteral (65843196346698543) 51200000000000000000),
            (exactRationalLiteral (872835814783993) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-4757499759178447277) 491520000000000000000),
            (exactRationalLiteral (-45140239920224759) 25600000000000000000),
            (exactRationalLiteral (-154238672695037) 160000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-45642094731500210237) 9830400000000000000000),
            (exactRationalLiteral (88707762392660341) 102400000000000000000),
            (exactRationalLiteral (312280120599571) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-7264506367667976901) 3276800000000000000000),
            (exactRationalLiteral (456530685774837111) 102400000000000000000),
            (exactRationalLiteral (-225008529793119) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-137196033713749050083) 9830400000000000000000),
            (exactRationalLiteral (960875157216360843) 102400000000000000000),
            (exactRationalLiteral (1833050441245453) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-465926486577535857709) 9830400000000000000000),
            (exactRationalLiteral (3446877824210099301) 102400000000000000000),
            (exactRationalLiteral (16821274565850659) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-221115612028962159429) 1638400000000000000000),
            (exactRationalLiteral (22490791574856128407) 51200000000000000000),
            (exactRationalLiteral (-183700033541727519) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (185608526041496589211) 153600000000000000000),
            (exactRationalLiteral (-385187898132029371) 200000000000000000),
            (exactRationalLiteral (-192272712818747) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-15579641372117636216009) 9830400000000000000000),
            (exactRationalLiteral (237283386116128141313) 102400000000000000000),
            (exactRationalLiteral (2717104083317037703) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3089181360941829956051) 4915200000000000000000),
            (exactRationalLiteral (-8814255383672616799) 10240000000000000000),
            (exactRationalLiteral (-2268680692725664093) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-33673080251901287323) 819200000000000000000),
            (exactRationalLiteral (-2734313383428013007) 25600000000000000000),
            (exactRationalLiteral (725868161978071983) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-5651569893427545915109) 9830400000000000000000),
            (exactRationalLiteral (52923296852743113789) 102400000000000000000),
            (exactRationalLiteral (-1565950226938567381) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (941707033209396150393) 819200000000000000000),
            (exactRationalLiteral (-21967396425950305971) 25600000000000000000),
            (exactRationalLiteral (422426083737605307) 800000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-5651569893427545915109) 9830400000000000000000),
            (exactRationalLiteral (52923296852743113789) 102400000000000000000),
            (exactRationalLiteral (-1565950226938567381) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-33673080251901287323) 819200000000000000000),
            (exactRationalLiteral (-2734313383428013007) 25600000000000000000),
            (exactRationalLiteral (725868161978071983) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (3089181360941829956051) 4915200000000000000000),
            (exactRationalLiteral (-8814255383672616799) 10240000000000000000),
            (exactRationalLiteral (-2268680692725664093) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-15579641372117636216009) 9830400000000000000000),
            (exactRationalLiteral (237283386116128141313) 102400000000000000000),
            (exactRationalLiteral (2717104083317037703) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (185608526041496589211) 153600000000000000000),
            (exactRationalLiteral (-385187898132029371) 200000000000000000),
            (exactRationalLiteral (-192272712818747) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-221115612028962159429) 1638400000000000000000),
            (exactRationalLiteral (22490791574856128407) 51200000000000000000),
            (exactRationalLiteral (-183700033541727519) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-465926486577535857709) 9830400000000000000000),
            (exactRationalLiteral (3446877824210099301) 102400000000000000000),
            (exactRationalLiteral (16821274565850659) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-137196033713749050083) 9830400000000000000000),
            (exactRationalLiteral (960875157216360843) 102400000000000000000),
            (exactRationalLiteral (1833050441245453) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-7264506367667976901) 3276800000000000000000),
            (exactRationalLiteral (456530685774837111) 102400000000000000000),
            (exactRationalLiteral (-225008529793119) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-45642094731500210237) 9830400000000000000000),
            (exactRationalLiteral (88707762392660341) 102400000000000000000),
            (exactRationalLiteral (312280120599571) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4757499759178447277) 491520000000000000000),
            (exactRationalLiteral (-45140239920224759) 25600000000000000000),
            (exactRationalLiteral (-154238672695037) 160000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (3388970693686340329) 4915200000000000000000),
            (exactRationalLiteral (65843196346698543) 51200000000000000000),
            (exactRationalLiteral (872835814783993) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (135281276505203023) 65536000000000000000),
            (exactRationalLiteral (37183796916720883) 51200000000000000000),
            (exactRationalLiteral (-233902497300939) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1567389855168955577) 9830400000000000000000),
            (exactRationalLiteral (37718022348922383) 102400000000000000000),
            (exactRationalLiteral (1637792037637481) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4524509740055462203) 9830400000000000000000),
            (exactRationalLiteral (-11395624264571609) 20480000000000000000),
            (exactRationalLiteral (-4586864212027147) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-12330387229849451801) 9830400000000000000000),
            (exactRationalLiteral (20379643111065053) 20480000000000000000),
            (exactRationalLiteral (15526496527113271) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1256713980727259507) 1228800000000000000000),
            (exactRationalLiteral (-93033054674939971) 12800000000000000000),
            (exactRationalLiteral (-8970232308547501) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-74055453933841982909) 4915200000000000000000),
            (exactRationalLiteral (881903938325484981) 51200000000000000000),
            (exactRationalLiteral (134406182744136979) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (105074865649952213081) 1638400000000000000000),
            (exactRationalLiteral (2161646046053476317) 51200000000000000000),
            (exactRationalLiteral (-250349753759058693) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-35031476061764153771) 614400000000000000000),
            (exactRationalLiteral (-186577378381880963) 1280000000000000000),
            (exactRationalLiteral (26650582805491369) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-2432996041716674003) 196608000000000000000),
            (exactRationalLiteral (6673563511388606643) 51200000000000000000),
            (exactRationalLiteral (-55146448623643019) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (13074845390165866223) 655360000000000000000),
            (exactRationalLiteral (-142425134811782241) 4096000000000000000),
            (exactRationalLiteral (-9805562242688451) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (166296404218134051) 819200000000000000000),
            (exactRationalLiteral (-55432134739378017) 25600000000000000000),
            (exactRationalLiteral (6159126082153113) 800000000000000000),
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
          (exactRationalLiteral (98299332731908153) 1600000000000000000),
          (exactRationalLiteral (626834893890236857) 9600000000000000000),
          (exactRationalLiteral (3179412859616242123) 204800000000000000000),
          (exactRationalLiteral (7547049479114963) 6144000000000000000),
          (exactRationalLiteral (1573804170901552093) 1228800000000000000000),
          (exactRationalLiteral (9198176893626791) 19200000000000000000),
          (exactRationalLiteral (1097357795877107) 6400000000000000000),
          (exactRationalLiteral (20033071550114327) 9600000000000000000),
          (exactRationalLiteral (2336663134519157) 3200000000000000000),
          (exactRationalLiteral (46728982124799383) 4800000000000000000),
          (exactRationalLiteral (5738394582296831681) 1228800000000000000000),
          (exactRationalLiteral (579090639373920031) 245760000000000000000),
          (exactRationalLiteral (5836352450040805349) 409600000000000000000),
          (exactRationalLiteral (19842232847566538427) 409600000000000000000),
          (exactRationalLiteral (3656622226927516739) 24576000000000000000),
          (exactRationalLiteral (16237057705756143991) 12800000000000000000),
          (exactRationalLiteral (2035299612793259064077) 1228800000000000000000),
          (exactRationalLiteral (401771212480123848623) 614400000000000000000),
          (exactRationalLiteral (104625683264204203) 2400000000000000000),
          (exactRationalLiteral (242298238893247799859) 409600000000000000000),
          (exactRationalLiteral (361539346406494358567) 307200000000000000000),
          (exactRationalLiteral (242298238893247799859) 409600000000000000000),
          (exactRationalLiteral (104625683264204203) 2400000000000000000),
          (exactRationalLiteral (401771212480123848623) 614400000000000000000),
          (exactRationalLiteral (2035299612793259064077) 1228800000000000000000),
          (exactRationalLiteral (16237057705756143991) 12800000000000000000),
          (exactRationalLiteral (3656622226927516739) 24576000000000000000),
          (exactRationalLiteral (19842232847566538427) 409600000000000000000),
          (exactRationalLiteral (5836352450040805349) 409600000000000000000),
          (exactRationalLiteral (579090639373920031) 245760000000000000000),
          (exactRationalLiteral (5738394582296831681) 1228800000000000000000),
          (exactRationalLiteral (46728982124799383) 4800000000000000000),
          (exactRationalLiteral (2336663134519157) 3200000000000000000),
          (exactRationalLiteral (20033071550114327) 9600000000000000000),
          (exactRationalLiteral (1097357795877107) 6400000000000000000),
          (exactRationalLiteral (9198176893626791) 19200000000000000000),
          (exactRationalLiteral (1573804170901552093) 1228800000000000000000),
          (exactRationalLiteral (7547049479114963) 6144000000000000000),
          (exactRationalLiteral (3179412859616242123) 204800000000000000000),
          (exactRationalLiteral (626834893890236857) 9600000000000000000),
          (exactRationalLiteral (98299332731908153) 1600000000000000000),
          (exactRationalLiteral (10123880490300337999) 614400000000000000000),
          (exactRationalLiteral (1722009914962508939) 81920000000000000000),
          (exactRationalLiteral (684347342461457) 2457600000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 52),
      (28, 4),
      (28, 20),
      (28, 36)
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
            (exactRationalLiteral (234731138464279751) 2457600000000000000000),
            (exactRationalLiteral (-33533019780611393) 25600000000000000000),
            (exactRationalLiteral (4790431397230199) 800000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (11620061251333429729) 655360000000000000000),
            (exactRationalLiteral (-738313735645455429) 20480000000000000000),
            (exactRationalLiteral (-3288468550583661) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-21605173362476086997) 4915200000000000000000),
            (exactRationalLiteral (6373029714690454291) 51200000000000000000),
            (exactRationalLiteral (-95120449725433157) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-40283060659369379377) 614400000000000000000),
            (exactRationalLiteral (-813319680594785911) 6400000000000000000),
            (exactRationalLiteral (33133022851818083) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (325038114941559822181) 4915200000000000000000),
            (exactRationalLiteral (1084166411262756221) 51200000000000000000),
            (exactRationalLiteral (-57678012727260271) 320000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-22362488223109718993) 1638400000000000000000),
            (exactRationalLiteral (290274878023433809) 10240000000000000000),
            (exactRationalLiteral (150329043151705053) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (117362656200520841) 245760000000000000000),
            (exactRationalLiteral (-130943775895352707) 12800000000000000000),
            (exactRationalLiteral (-9985128301658867) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-11525232135965509271) 9830400000000000000000),
            (exactRationalLiteral (167728122777094193) 102400000000000000000),
            (exactRationalLiteral (17388457083771193) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-4923515821551329941) 9830400000000000000000),
            (exactRationalLiteral (-15274613935632697) 20480000000000000000),
            (exactRationalLiteral (-5110609965625573) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1814025702822949111) 9830400000000000000000),
            (exactRationalLiteral (44606295053877039) 102400000000000000000),
            (exactRationalLiteral (1806344314839847) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (10366289389503331691) 4915200000000000000000),
            (exactRationalLiteral (7239407393542519) 10240000000000000000),
            (exactRationalLiteral (-51895495440641) 320000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3794470177149037223) 4915200000000000000000),
            (exactRationalLiteral (554541419267067) 409600000000000000),
            (exactRationalLiteral (864404716058423) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-24067640573006870191) 2457600000000000000000),
            (exactRationalLiteral (-9649604397983403) 5120000000000000000),
            (exactRationalLiteral (-782697671370943) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-45107096955230966131) 9830400000000000000000),
            (exactRationalLiteral (89458803108102229) 102400000000000000000),
            (exactRationalLiteral (63240237121373) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19058319978400586689) 9830400000000000000000),
            (exactRationalLiteral (454988207811584023) 102400000000000000000),
            (exactRationalLiteral (-21849218073337) 128000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8760959735327765507) 655360000000000000000),
            (exactRationalLiteral (965402426601071147) 102400000000000000000),
            (exactRationalLiteral (430584251109699) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-148355969138819501697) 3276800000000000000000),
            (exactRationalLiteral (3501891382986776389) 102400000000000000000),
            (exactRationalLiteral (2137100964497577) 640000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-530973411252864024193) 4915200000000000000000),
            (exactRationalLiteral (21572529334382425271) 51200000000000000000),
            (exactRationalLiteral (-275431086695124049) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (11145288675615348953) 10240000000000000000),
            (exactRationalLiteral (-762801759523767507) 400000000000000000),
            (exactRationalLiteral (15340346193401217) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-14130882333381039029479) 9830400000000000000000),
            (exactRationalLiteral (244378538969408235233) 102400000000000000000),
            (exactRationalLiteral (830472343323009257) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2800885129340954897149) 4915200000000000000000),
            (exactRationalLiteral (-2058728023130401331) 2048000000000000000),
            (exactRationalLiteral (-1429781137222810547) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-109451689052466426863) 2457600000000000000000),
            (exactRationalLiteral (-199333705481400399) 25600000000000000000),
            (exactRationalLiteral (541621676995234321) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1783953574954500045657) 3276800000000000000000),
            (exactRationalLiteral (47139891030413796253) 102400000000000000000),
            (exactRationalLiteral (-1325752684226091387) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2698192201319716410853) 2457600000000000000000),
            (exactRationalLiteral (-4074901693962123767) 5120000000000000000),
            (exactRationalLiteral (374017894332238261) 800000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1783953574954500045657) 3276800000000000000000),
            (exactRationalLiteral (47139891030413796253) 102400000000000000000),
            (exactRationalLiteral (-1325752684226091387) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-109451689052466426863) 2457600000000000000000),
            (exactRationalLiteral (-199333705481400399) 25600000000000000000),
            (exactRationalLiteral (541621676995234321) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (2800885129340954897149) 4915200000000000000000),
            (exactRationalLiteral (-2058728023130401331) 2048000000000000000),
            (exactRationalLiteral (-1429781137222810547) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-14130882333381039029479) 9830400000000000000000),
            (exactRationalLiteral (244378538969408235233) 102400000000000000000),
            (exactRationalLiteral (830472343323009257) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (11145288675615348953) 10240000000000000000),
            (exactRationalLiteral (-762801759523767507) 400000000000000000),
            (exactRationalLiteral (15340346193401217) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-530973411252864024193) 4915200000000000000000),
            (exactRationalLiteral (21572529334382425271) 51200000000000000000),
            (exactRationalLiteral (-275431086695124049) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-148355969138819501697) 3276800000000000000000),
            (exactRationalLiteral (3501891382986776389) 102400000000000000000),
            (exactRationalLiteral (2137100964497577) 640000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8760959735327765507) 655360000000000000000),
            (exactRationalLiteral (965402426601071147) 102400000000000000000),
            (exactRationalLiteral (430584251109699) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19058319978400586689) 9830400000000000000000),
            (exactRationalLiteral (454988207811584023) 102400000000000000000),
            (exactRationalLiteral (-21849218073337) 128000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-45107096955230966131) 9830400000000000000000),
            (exactRationalLiteral (89458803108102229) 102400000000000000000),
            (exactRationalLiteral (63240237121373) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-24067640573006870191) 2457600000000000000000),
            (exactRationalLiteral (-9649604397983403) 5120000000000000000),
            (exactRationalLiteral (-782697671370943) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (3794470177149037223) 4915200000000000000000),
            (exactRationalLiteral (554541419267067) 409600000000000000),
            (exactRationalLiteral (864404716058423) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (10366289389503331691) 4915200000000000000000),
            (exactRationalLiteral (7239407393542519) 10240000000000000000),
            (exactRationalLiteral (-51895495440641) 320000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1814025702822949111) 9830400000000000000000),
            (exactRationalLiteral (44606295053877039) 102400000000000000000),
            (exactRationalLiteral (1806344314839847) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4923515821551329941) 9830400000000000000000),
            (exactRationalLiteral (-15274613935632697) 20480000000000000000),
            (exactRationalLiteral (-5110609965625573) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-11525232135965509271) 9830400000000000000000),
            (exactRationalLiteral (167728122777094193) 102400000000000000000),
            (exactRationalLiteral (17388457083771193) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (117362656200520841) 245760000000000000000),
            (exactRationalLiteral (-130943775895352707) 12800000000000000000),
            (exactRationalLiteral (-9985128301658867) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-22362488223109718993) 1638400000000000000000),
            (exactRationalLiteral (290274878023433809) 10240000000000000000),
            (exactRationalLiteral (150329043151705053) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (325038114941559822181) 4915200000000000000000),
            (exactRationalLiteral (1084166411262756221) 51200000000000000000),
            (exactRationalLiteral (-57678012727260271) 320000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-40283060659369379377) 614400000000000000000),
            (exactRationalLiteral (-813319680594785911) 6400000000000000000),
            (exactRationalLiteral (33133022851818083) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-21605173362476086997) 4915200000000000000000),
            (exactRationalLiteral (6373029714690454291) 51200000000000000000),
            (exactRationalLiteral (-95120449725433157) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (11620061251333429729) 655360000000000000000),
            (exactRationalLiteral (-738313735645455429) 20480000000000000000),
            (exactRationalLiteral (-3288468550583661) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (234731138464279751) 2457600000000000000000),
            (exactRationalLiteral (-33533019780611393) 25600000000000000000),
            (exactRationalLiteral (4790431397230199) 800000000000000000),
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
          (exactRationalLiteral (2663773713285944969) 38400000000000000000),
          (exactRationalLiteral (13641934326229190227) 204800000000000000000),
          (exactRationalLiteral (138669066680526041) 9600000000000000000),
          (exactRationalLiteral (19331800776779) 25000000000000000),
          (exactRationalLiteral (23392933815085561) 19200000000000000000),
          (exactRationalLiteral (646028591669937041) 1228800000000000000000),
          (exactRationalLiteral (244168487133462619) 1228800000000000000000),
          (exactRationalLiteral (436420386686871197) 204800000000000000000),
          (exactRationalLiteral (500626525996624979) 614400000000000000000),
          (exactRationalLiteral (3026842310518085243) 307200000000000000000),
          (exactRationalLiteral (1181644768851619) 256000000000000000),
          (exactRationalLiteral (7978422922746023) 3840000000000000000),
          (exactRationalLiteral (262321504538811131) 19200000000000000000),
          (exactRationalLiteral (889723549152499393) 19200000000000000000),
          (exactRationalLiteral (1164983255838906199) 9600000000000000000),
          (exactRationalLiteral (2755800093400664657) 2400000000000000000),
          (exactRationalLiteral (9674858865487824019) 6400000000000000000),
          (exactRationalLiteral (384190226287280617) 640000000000000000),
          (exactRationalLiteral (860160321816028459) 19200000000000000000),
          (exactRationalLiteral (10737065927302296949) 19200000000000000000),
          (exactRationalLiteral (5391527313489936847) 4800000000000000000),
          (exactRationalLiteral (10737065927302296949) 19200000000000000000),
          (exactRationalLiteral (860160321816028459) 19200000000000000000),
          (exactRationalLiteral (384190226287280617) 640000000000000000),
          (exactRationalLiteral (9674858865487824019) 6400000000000000000),
          (exactRationalLiteral (2755800093400664657) 2400000000000000000),
          (exactRationalLiteral (1164983255838906199) 9600000000000000000),
          (exactRationalLiteral (889723549152499393) 19200000000000000000),
          (exactRationalLiteral (262321504538811131) 19200000000000000000),
          (exactRationalLiteral (7978422922746023) 3840000000000000000),
          (exactRationalLiteral (1181644768851619) 256000000000000000),
          (exactRationalLiteral (3026842310518085243) 307200000000000000000),
          (exactRationalLiteral (500626525996624979) 614400000000000000000),
          (exactRationalLiteral (436420386686871197) 204800000000000000000),
          (exactRationalLiteral (244168487133462619) 1228800000000000000000),
          (exactRationalLiteral (646028591669937041) 1228800000000000000000),
          (exactRationalLiteral (23392933815085561) 19200000000000000000),
          (exactRationalLiteral (19331800776779) 25000000000000000),
          (exactRationalLiteral (138669066680526041) 9600000000000000000),
          (exactRationalLiteral (13641934326229190227) 204800000000000000000),
          (exactRationalLiteral (2663773713285944969) 38400000000000000000),
          (exactRationalLiteral (80057884482759481) 9600000000000000000),
          (exactRationalLiteral (24128906906535711) 1280000000000000000),
          (exactRationalLiteral (684347342461457) 4800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 51),
      (28, 3),
      (28, 19),
      (28, 35)
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
            (exactRationalLiteral (684347342461457) 19660800000000000000),
            (exactRationalLiteral (-684347342461457) 1024000000000000000),
            (exactRationalLiteral (684347342461457) 160000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (10138969364096323947) 655360000000000000000),
            (exactRationalLiteral (-738433422463580493) 20480000000000000000),
            (exactRationalLiteral (3228625141521129) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (15331663524554280313) 4915200000000000000000),
            (exactRationalLiteral (5912599913585141387) 51200000000000000000),
            (exactRationalLiteral (-27018890165444659) 320000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-14913150902843656997) 204800000000000000000),
            (exactRationalLiteral (-667822709094860151) 6400000000000000000),
            (exactRationalLiteral (39615462898144797) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (327930271405991772599) 4915200000000000000000),
            (exactRationalLiteral (-145474463036934523) 51200000000000000000),
            (exactRationalLiteral (-326430373513544017) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-56511578369175409777) 4915200000000000000000),
            (exactRationalLiteral (416907256707825081) 10240000000000000000),
            (exactRationalLiteral (166251903559273127) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-21515366530790927) 81920000000000000000),
            (exactRationalLiteral (-172914081088210907) 12800000000000000000),
            (exactRationalLiteral (-11000024294770233) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-10302754072071058109) 9830400000000000000000),
            (exactRationalLiteral (241005872225494809) 102400000000000000000),
            (exactRationalLiteral (3850083528085823) 640000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-5445176542222211431) 9830400000000000000000),
            (exactRationalLiteral (-97863001047862629) 102400000000000000000),
            (exactRationalLiteral (-5634355719223999) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (701337938011032991) 3276800000000000000000),
            (exactRationalLiteral (52168776867641159) 102400000000000000000),
            (exactRationalLiteral (1974896592042213) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (10580255581663559737) 4915200000000000000000),
            (exactRationalLiteral (35107977099095243) 51200000000000000000),
            (exactRationalLiteral (-285052457105471) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1406905124599045423) 1638400000000000000000),
            (exactRationalLiteral (72758434075165927) 51200000000000000000),
            (exactRationalLiteral (855973617332853) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-24366567094234406629) 2457600000000000000000),
            (exactRationalLiteral (-51401821291192303) 25600000000000000000),
            (exactRationalLiteral (-794201979266701) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-14856860471090269691) 3276800000000000000000),
            (exactRationalLiteral (3568547371585253) 4096000000000000000),
            (exactRationalLiteral (-7431985854273) 128000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-130689843077129959) 78643200000000000000),
            (exactRationalLiteral (452160842160169711) 102400000000000000000),
            (exactRationalLiteral (-867452373873731) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-125622424324057282351) 9830400000000000000000),
            (exactRationalLiteral (192863966245047687) 20480000000000000000),
            (exactRationalLiteral (-194376387805211) 640000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-423952876139641443233) 9830400000000000000000),
            (exactRationalLiteral (3532361862790002381) 102400000000000000000),
            (exactRationalLiteral (4549735079125111) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-16208413299980981891) 196608000000000000000),
            (exactRationalLiteral (4057468576259027203) 10240000000000000000),
            (exactRationalLiteral (-367162139848520579) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (149118302535605508587) 153600000000000000000),
            (exactRationalLiteral (-184923775969314077) 100000000000000000),
            (exactRationalLiteral (30872965099621181) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-4220730652801563206927) 3276800000000000000000),
            (exactRationalLiteral (243927164862712215369) 102400000000000000000),
            (exactRationalLiteral (-1056159396671019189) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (826091383482244128373) 1638400000000000000000),
            (exactRationalLiteral (-55509526016145568371) 51200000000000000000),
            (exactRationalLiteral (-590881581719957001) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-104885217101343368053) 2457600000000000000000),
            (exactRationalLiteral (1598660032533861561) 25600000000000000000),
            (exactRationalLiteral (357375192012396659) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-5083969620720880552121) 9830400000000000000000),
            (exactRationalLiteral (42317275378934382693) 102400000000000000000),
            (exactRationalLiteral (-1085555141513615393) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2580239732475218088791) 2457600000000000000000),
            (exactRationalLiteral (-18975253271292399883) 25600000000000000000),
            (exactRationalLiteral (65121940985374243) 160000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-5083969620720880552121) 9830400000000000000000),
            (exactRationalLiteral (42317275378934382693) 102400000000000000000),
            (exactRationalLiteral (-1085555141513615393) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-104885217101343368053) 2457600000000000000000),
            (exactRationalLiteral (1598660032533861561) 25600000000000000000),
            (exactRationalLiteral (357375192012396659) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (826091383482244128373) 1638400000000000000000),
            (exactRationalLiteral (-55509526016145568371) 51200000000000000000),
            (exactRationalLiteral (-590881581719957001) 1600000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4220730652801563206927) 3276800000000000000000),
            (exactRationalLiteral (243927164862712215369) 102400000000000000000),
            (exactRationalLiteral (-1056159396671019189) 3200000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (149118302535605508587) 153600000000000000000),
            (exactRationalLiteral (-184923775969314077) 100000000000000000),
            (exactRationalLiteral (30872965099621181) 50000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-16208413299980981891) 196608000000000000000),
            (exactRationalLiteral (4057468576259027203) 10240000000000000000),
            (exactRationalLiteral (-367162139848520579) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-423952876139641443233) 9830400000000000000000),
            (exactRationalLiteral (3532361862790002381) 102400000000000000000),
            (exactRationalLiteral (4549735079125111) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-125622424324057282351) 9830400000000000000000),
            (exactRationalLiteral (192863966245047687) 20480000000000000000),
            (exactRationalLiteral (-194376387805211) 640000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-130689843077129959) 78643200000000000000),
            (exactRationalLiteral (452160842160169711) 102400000000000000000),
            (exactRationalLiteral (-867452373873731) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-14856860471090269691) 3276800000000000000000),
            (exactRationalLiteral (3568547371585253) 4096000000000000000),
            (exactRationalLiteral (-7431985854273) 128000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-24366567094234406629) 2457600000000000000000),
            (exactRationalLiteral (-51401821291192303) 25600000000000000000),
            (exactRationalLiteral (-794201979266701) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (1406905124599045423) 1638400000000000000000),
            (exactRationalLiteral (72758434075165927) 51200000000000000000),
            (exactRationalLiteral (855973617332853) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (10580255581663559737) 4915200000000000000000),
            (exactRationalLiteral (35107977099095243) 51200000000000000000),
            (exactRationalLiteral (-285052457105471) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (701337938011032991) 3276800000000000000000),
            (exactRationalLiteral (52168776867641159) 102400000000000000000),
            (exactRationalLiteral (1974896592042213) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5445176542222211431) 9830400000000000000000),
            (exactRationalLiteral (-97863001047862629) 102400000000000000000),
            (exactRationalLiteral (-5634355719223999) 3200000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-10302754072071058109) 9830400000000000000000),
            (exactRationalLiteral (241005872225494809) 102400000000000000000),
            (exactRationalLiteral (3850083528085823) 640000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-21515366530790927) 81920000000000000000),
            (exactRationalLiteral (-172914081088210907) 12800000000000000000),
            (exactRationalLiteral (-11000024294770233) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-56511578369175409777) 4915200000000000000000),
            (exactRationalLiteral (416907256707825081) 10240000000000000000),
            (exactRationalLiteral (166251903559273127) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (327930271405991772599) 4915200000000000000000),
            (exactRationalLiteral (-145474463036934523) 51200000000000000000),
            (exactRationalLiteral (-326430373513544017) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-14913150902843656997) 204800000000000000000),
            (exactRationalLiteral (-667822709094860151) 6400000000000000000),
            (exactRationalLiteral (39615462898144797) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (15331663524554280313) 4915200000000000000000),
            (exactRationalLiteral (5912599913585141387) 51200000000000000000),
            (exactRationalLiteral (-27018890165444659) 320000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (10138969364096323947) 655360000000000000000),
            (exactRationalLiteral (-738433422463580493) 20480000000000000000),
            (exactRationalLiteral (3228625141521129) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (684347342461457) 19660800000000000000),
            (exactRationalLiteral (-684347342461457) 1024000000000000000),
            (exactRationalLiteral (684347342461457) 160000000000000000),
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
          (exactRationalLiteral (6159126082153113) 102400000000000000000),
          (exactRationalLiteral (1359943153677426013) 81920000000000000000),
          (exactRationalLiteral (102013102850866061) 15360000000000000000),
          (exactRationalLiteral (1456901038346811053) 19200000000000000000),
          (exactRationalLiteral (6841315751825075621) 102400000000000000000),
          (exactRationalLiteral (7784299117414843831) 614400000000000000000),
          (exactRationalLiteral (13671566595427547) 19200000000000000000),
          (exactRationalLiteral (1371118927013073019) 1228800000000000000000),
          (exactRationalLiteral (89936413834379227) 153600000000000000000),
          (exactRationalLiteral (35414517352355473) 153600000000000000000),
          (exactRationalLiteral (33389723650311181) 15360000000000000000),
          (exactRationalLiteral (69399287208207341) 76800000000000000000),
          (exactRationalLiteral (76634877863124161) 7680000000000000000),
          (exactRationalLiteral (5604831918142129303) 1228800000000000000000),
          (exactRationalLiteral (737298110720098127) 409600000000000000000),
          (exactRationalLiteral (16064699778806875993) 1228800000000000000000),
          (exactRationalLiteral (54316655579737799207) 1228800000000000000000),
          (exactRationalLiteral (19463665918182450783) 204800000000000000000),
          (exactRationalLiteral (39519874091994584461) 38400000000000000000),
          (exactRationalLiteral (1674524826914105288779) 1228800000000000000000),
          (exactRationalLiteral (330326329246532224057) 614400000000000000000),
          (exactRationalLiteral (4521539515850680997) 102400000000000000000),
          (exactRationalLiteral (651787276381697598047) 1228800000000000000000),
          (exactRationalLiteral (109923605229107441067) 102400000000000000000),
          (exactRationalLiteral (651787276381697598047) 1228800000000000000000),
          (exactRationalLiteral (4521539515850680997) 102400000000000000000),
          (exactRationalLiteral (330326329246532224057) 614400000000000000000),
          (exactRationalLiteral (1674524826914105288779) 1228800000000000000000),
          (exactRationalLiteral (39519874091994584461) 38400000000000000000),
          (exactRationalLiteral (19463665918182450783) 204800000000000000000),
          (exactRationalLiteral (54316655579737799207) 1228800000000000000000),
          (exactRationalLiteral (16064699778806875993) 1228800000000000000000),
          (exactRationalLiteral (737298110720098127) 409600000000000000000),
          (exactRationalLiteral (5604831918142129303) 1228800000000000000000),
          (exactRationalLiteral (76634877863124161) 7680000000000000000),
          (exactRationalLiteral (69399287208207341) 76800000000000000000),
          (exactRationalLiteral (33389723650311181) 15360000000000000000),
          (exactRationalLiteral (35414517352355473) 153600000000000000000),
          (exactRationalLiteral (89936413834379227) 153600000000000000000),
          (exactRationalLiteral (1371118927013073019) 1228800000000000000000),
          (exactRationalLiteral (13671566595427547) 19200000000000000000),
          (exactRationalLiteral (7784299117414843831) 614400000000000000000),
          (exactRationalLiteral (6841315751825075621) 102400000000000000000),
          (exactRationalLiteral (1456901038346811053) 19200000000000000000),
          (exactRationalLiteral (102013102850866061) 15360000000000000000),
          (exactRationalLiteral (1359943153677426013) 81920000000000000000),
          (exactRationalLiteral (6159126082153113) 102400000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 50),
      (28, 2),
      (28, 18),
      (28, 34)
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
            (exactRationalLiteral (6159126082153113) 819200000000000000000),
            (exactRationalLiteral (-6159126082153113) 25600000000000000000),
            (exactRationalLiteral (2053042027384371) 800000000000000000),
            (exactRationalLiteral (-684347342461457) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (8683706477991387197) 655360000000000000000),
            (exactRationalLiteral (-712484734513286397) 20480000000000000000),
            (exactRationalLiteral (9745718833625919) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (49026233591731288543) 4915200000000000000000),
            (exactRationalLiteral (5292274108072667931) 51200000000000000000),
            (exactRationalLiteral (-175068451929013433) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-48245073648137087477) 614400000000000000000),
            (exactRationalLiteral (-99279195481925507) 1280000000000000000),
            (exactRationalLiteral (46097902944471511) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (107662699635366222203) 1638400000000000000000),
            (exactRationalLiteral (-305455315369119183) 10240000000000000000),
            (exactRationalLiteral (-364470683390786679) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-41945646383599107527) 4915200000000000000000),
            (exactRationalLiteral (2781389618591354061) 51200000000000000000),
            (exactRationalLiteral (182174763966841201) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1496274860000817607) 1228800000000000000000),
            (exactRationalLiteral (-218943970253514571) 12800000000000000000),
            (exactRationalLiteral (-12014920287881599) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-8618265984806308187) 9830400000000000000000),
            (exactRationalLiteral (321731463900527113) 102400000000000000000),
            (exactRationalLiteral (21112378197087037) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-6102061800154468897) 9830400000000000000000),
            (exactRationalLiteral (-121447915431955477) 102400000000000000000),
            (exactRationalLiteral (-246324058912897) 128000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2441399443452261947) 9830400000000000000000),
            (exactRationalLiteral (60405467790214743) 102400000000000000000),
            (exactRationalLiteral (2143448869244579) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3595793504951085493) 1638400000000000000000),
            (exactRationalLiteral (33916617310868827) 51200000000000000000),
            (exactRationalLiteral (-310627437007737) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (4667503937261223787) 4915200000000000000000),
            (exactRationalLiteral (76165466347046199) 51200000000000000000),
            (exactRationalLiteral (847542518607283) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-24684554462964343891) 2457600000000000000000),
            (exactRationalLiteral (-54601637824050623) 25600000000000000000),
            (exactRationalLiteral (-805706287162459) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-8807705012564643163) 1966080000000000000000),
            (exactRationalLiteral (87972405937247629) 102400000000000000000),
            (exactRationalLiteral (-434839529835023) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-908997309856991507) 655360000000000000000),
            (exactRationalLiteral (17921943552823767) 4096000000000000000),
            (exactRationalLiteral (-1188674295914037) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-119853777784734707417) 9830400000000000000000),
            (exactRationalLiteral (957627371088862707) 102400000000000000000),
            (exactRationalLiteral (-2374348129161809) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-402728651220925378711) 9830400000000000000000),
            (exactRationalLiteral (3538289263619777277) 102400000000000000000),
            (exactRationalLiteral (-1586034664237663) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-96086381700849854751) 1638400000000000000000),
            (exactRationalLiteral (18635232215594260639) 51200000000000000000),
            (exactRationalLiteral (-458893193001917109) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (131798226099371691223) 153600000000000000000),
            (exactRationalLiteral (-140211165864905029) 80000000000000000),
            (exactRationalLiteral (9281116801168229) 10000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-11218849408948444672619) 9830400000000000000000),
            (exactRationalLiteral (235929263796040081721) 102400000000000000000),
            (exactRationalLiteral (-588558227333009527) 640000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (428296402718246181013) 983040000000000000000),
            (exactRationalLiteral (-56195253232019689283) 51200000000000000000),
            (exactRationalLiteral (49603594756579309) 320000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-30580580180640929809) 819200000000000000000),
            (exactRationalLiteral (2659667830617772873) 25600000000000000000),
            (exactRationalLiteral (173128707029558997) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-4842131839974587736703) 9830400000000000000000),
            (exactRationalLiteral (38455449898304873109) 102400000000000000000),
            (exactRationalLiteral (-845357598801139399) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (823367298849654891963) 819200000000000000000),
            (exactRationalLiteral (-3553926166079129823) 5120000000000000000),
            (exactRationalLiteral (277201515521504169) 800000000000000000),
            (exactRationalLiteral (-24204094702683523) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-4842131839974587736703) 9830400000000000000000),
            (exactRationalLiteral (38455449898304873109) 102400000000000000000),
            (exactRationalLiteral (-845357598801139399) 3200000000000000000),
            (exactRationalLiteral (120098771356237997) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-30580580180640929809) 819200000000000000000),
            (exactRationalLiteral (2659667830617772873) 25600000000000000000),
            (exactRationalLiteral (173128707029558997) 800000000000000000),
            (exactRationalLiteral (-92123242491418831) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (428296402718246181013) 983040000000000000000),
            (exactRationalLiteral (-56195253232019689283) 51200000000000000000),
            (exactRationalLiteral (49603594756579309) 320000000000000000),
            (exactRationalLiteral (419449777751426773) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-11218849408948444672619) 9830400000000000000000),
            (exactRationalLiteral (235929263796040081721) 102400000000000000000),
            (exactRationalLiteral (-588558227333009527) 640000000000000000),
            (exactRationalLiteral (-943315869997014223) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (131798226099371691223) 153600000000000000000),
            (exactRationalLiteral (-140211165864905029) 80000000000000000),
            (exactRationalLiteral (9281116801168229) 10000000000000000),
            (exactRationalLiteral (3883154726554991) 2343750000000000)
          ],
          ![
            (exactRationalLiteral (-96086381700849854751) 1638400000000000000000),
            (exactRationalLiteral (18635232215594260639) 51200000000000000000),
            (exactRationalLiteral (-458893193001917109) 1600000000000000000),
            (exactRationalLiteral (-9173105315339653) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-402728651220925378711) 9830400000000000000000),
            (exactRationalLiteral (3538289263619777277) 102400000000000000000),
            (exactRationalLiteral (-1586034664237663) 3200000000000000000),
            (exactRationalLiteral (-3067884871681387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-119853777784734707417) 9830400000000000000000),
            (exactRationalLiteral (957627371088862707) 102400000000000000000),
            (exactRationalLiteral (-2374348129161809) 3200000000000000000),
            (exactRationalLiteral (-701233095067877) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-908997309856991507) 655360000000000000000),
            (exactRationalLiteral (17921943552823767) 4096000000000000000),
            (exactRationalLiteral (-1188674295914037) 3200000000000000000),
            (exactRationalLiteral (-160610961020153) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8807705012564643163) 1966080000000000000000),
            (exactRationalLiteral (87972405937247629) 102400000000000000000),
            (exactRationalLiteral (-434839529835023) 3200000000000000000),
            (exactRationalLiteral (-124519941739099) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-24684554462964343891) 2457600000000000000000),
            (exactRationalLiteral (-54601637824050623) 25600000000000000000),
            (exactRationalLiteral (-805706287162459) 800000000000000000),
            (exactRationalLiteral (-1917384649293) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (4667503937261223787) 4915200000000000000000),
            (exactRationalLiteral (76165466347046199) 51200000000000000000),
            (exactRationalLiteral (847542518607283) 1600000000000000000),
            (exactRationalLiteral (-843109872557) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (3595793504951085493) 1638400000000000000000),
            (exactRationalLiteral (33916617310868827) 51200000000000000000),
            (exactRationalLiteral (-310627437007737) 1600000000000000000),
            (exactRationalLiteral (-12787489951133) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2441399443452261947) 9830400000000000000000),
            (exactRationalLiteral (60405467790214743) 102400000000000000000),
            (exactRationalLiteral (2143448869244579) 3200000000000000000),
            (exactRationalLiteral (84276138601183) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6102061800154468897) 9830400000000000000000),
            (exactRationalLiteral (-121447915431955477) 102400000000000000000),
            (exactRationalLiteral (-246324058912897) 128000000000000000),
            (exactRationalLiteral (-87290958933071) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-8618265984806308187) 9830400000000000000000),
            (exactRationalLiteral (321731463900527113) 102400000000000000000),
            (exactRationalLiteral (21112378197087037) 3200000000000000000),
            (exactRationalLiteral (310326759442987) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1496274860000817607) 1228800000000000000000),
            (exactRationalLiteral (-218943970253514571) 12800000000000000000),
            (exactRationalLiteral (-12014920287881599) 400000000000000000),
            (exactRationalLiteral (-507447996555683) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-41945646383599107527) 4915200000000000000000),
            (exactRationalLiteral (2781389618591354061) 51200000000000000000),
            (exactRationalLiteral (182174763966841201) 1600000000000000000),
            (exactRationalLiteral (7961430203784037) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (107662699635366222203) 1638400000000000000000),
            (exactRationalLiteral (-305455315369119183) 10240000000000000000),
            (exactRationalLiteral (-364470683390786679) 1600000000000000000),
            (exactRationalLiteral (-19020154938621331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-48245073648137087477) 614400000000000000000),
            (exactRationalLiteral (-99279195481925507) 1280000000000000000),
            (exactRationalLiteral (46097902944471511) 200000000000000000),
            (exactRationalLiteral (3241220023163357) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (49026233591731288543) 4915200000000000000000),
            (exactRationalLiteral (5292274108072667931) 51200000000000000000),
            (exactRationalLiteral (-175068451929013433) 1600000000000000000),
            (exactRationalLiteral (-6662333516965023) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (8683706477991387197) 655360000000000000000),
            (exactRationalLiteral (-712484734513286397) 20480000000000000000),
            (exactRationalLiteral (9745718833625919) 640000000000000000),
            (exactRationalLiteral (217236456403493) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (6159126082153113) 819200000000000000000),
            (exactRationalLiteral (-6159126082153113) 25600000000000000000),
            (exactRationalLiteral (2053042027384371) 800000000000000000),
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
          (exactRationalLiteral (8044732944951419621) 614400000000000000000),
          (exactRationalLiteral (258295451309944751) 3200000000000000000),
          (exactRationalLiteral (5101492761584401807) 76800000000000000000),
          (exactRationalLiteral (259121106133731407) 25600000000000000000),
          (exactRationalLiteral (3649431632702603) 2048000000000000000),
          (exactRationalLiteral (148766472221796209) 153600000000000000000),
          (exactRationalLiteral (810642715468200227) 1228800000000000000000),
          (exactRationalLiteral (109547102898718379) 409600000000000000000),
          (exactRationalLiteral (1361023212123111077) 614400000000000000000),
          (exactRationalLiteral (204105781179534227) 204800000000000000000),
          (exactRationalLiteral (3106347780931491377) 307200000000000000000),
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
          (exactRationalLiteral (3106347780931491377) 307200000000000000000),
          (exactRationalLiteral (204105781179534227) 204800000000000000000),
          (exactRationalLiteral (1361023212123111077) 614400000000000000000),
          (exactRationalLiteral (109547102898718379) 409600000000000000000),
          (exactRationalLiteral (810642715468200227) 1228800000000000000000),
          (exactRationalLiteral (148766472221796209) 153600000000000000000),
          (exactRationalLiteral (3649431632702603) 2048000000000000000),
          (exactRationalLiteral (259121106133731407) 25600000000000000000),
          (exactRationalLiteral (5101492761584401807) 76800000000000000000),
          (exactRationalLiteral (258295451309944751) 3200000000000000000),
          (exactRationalLiteral (8044732944951419621) 614400000000000000000),
          (exactRationalLiteral (146950792954004407) 10240000000000000000),
          (exactRationalLiteral (684347342461457) 38400000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 49),
      (28, 1),
      (28, 17),
      (28, 33)
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
theorem generatorCoordinates20_valid : ∀ i, (generatorCoordinates20 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
