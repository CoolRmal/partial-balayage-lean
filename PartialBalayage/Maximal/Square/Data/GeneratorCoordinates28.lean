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

/-- Actual coordinate interval candidates, block 28. -/
def generatorCoordinates28 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 6
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
            (exactRationalLiteral (3710615129098238777) 4915200000000000000000),
            (exactRationalLiteral (-285431933007556829) 51200000000000000000),
            (exactRationalLiteral (21956302539042833) 1600000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (27971429456450109079) 983040000000000000000),
            (exactRationalLiteral (-340795727569170403) 10240000000000000000),
            (exactRationalLiteral (-14026114969979873) 320000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-372748074142113570739) 9830400000000000000000),
            (exactRationalLiteral (15963038263642173023) 102400000000000000000),
            (exactRationalLiteral (69249716323894469) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-45191937615356116877) 1228800000000000000000),
            (exactRationalLiteral (-102771362173396479) 512000000000000000),
            (exactRationalLiteral (5851531935314063) 80000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (604621963607952050633) 9830400000000000000000),
            (exactRationalLiteral (1835963577270717079) 20480000000000000000),
            (exactRationalLiteral (-377187799960005151) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-20697461469953906083) 1228800000000000000000),
            (exactRationalLiteral (-9131742342895997) 2560000000000000000),
            (exactRationalLiteral (27323258493654101) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2333587866154300123) 1638400000000000000000),
            (exactRationalLiteral (-80282167349083509) 51200000000000000000),
            (exactRationalLiteral (-29558382215697303) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3952992349591718273) 9830400000000000000000),
            (exactRationalLiteral (-46004366840156347) 102400000000000000000),
            (exactRationalLiteral (14275184796452071) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (46407880053979210621) 9830400000000000000000),
            (exactRationalLiteral (232390308537573039) 102400000000000000000),
            (exactRationalLiteral (-3932091579710987) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9602748106133104037) 2457600000000000000000),
            (exactRationalLiteral (66557009776104063) 25600000000000000000),
            (exactRationalLiteral (1853178041964269) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-151258600562848652713) 9830400000000000000000),
            (exactRationalLiteral (-477425784936583187) 102400000000000000000),
            (exactRationalLiteral (-8333248349840833) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-43828998844108247) 6553600000000000000),
            (exactRationalLiteral (-129145343462731971) 25600000000000000000),
            (exactRationalLiteral (-2065593022578393) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (10613609923828766187) 1638400000000000000000),
            (exactRationalLiteral (365207265053627883) 51200000000000000000),
            (exactRationalLiteral (5964000765172473) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (130141731641346947) 2457600000000000000000),
            (exactRationalLiteral (94854606023361121) 25600000000000000000),
            (exactRationalLiteral (-3821155172399509) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-60642586195817746339) 9830400000000000000000),
            (exactRationalLiteral (79047597554828547) 20480000000000000000),
            (exactRationalLiteral (-10023506316916651) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (102716965380684691357) 4915200000000000000000),
            (exactRationalLiteral (-31073997829964089) 2048000000000000000),
            (exactRationalLiteral (3961941001854737) 320000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (56796156525343369561) 819200000000000000000),
            (exactRationalLiteral (-272438055191280987) 5120000000000000000),
            (exactRationalLiteral (4400869851370839) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-288682821091390792121) 4915200000000000000000),
            (exactRationalLiteral (3413580955815315213) 51200000000000000000),
            (exactRationalLiteral (-15922768667224957) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-16982203990389349537) 655360000000000000000),
            (exactRationalLiteral (208599982360074763) 102400000000000000000),
            (exactRationalLiteral (40126429011847017) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8533676949283801711) 2457600000000000000000),
            (exactRationalLiteral (-132884395579376853) 25600000000000000000),
            (exactRationalLiteral (3384215964967721) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-277804460466121114133) 1638400000000000000000),
            (exactRationalLiteral (4858029095944351019) 51200000000000000000),
            (exactRationalLiteral (-10294728599152923) 320000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1772753193190383112343) 4915200000000000000000),
            (exactRationalLiteral (-2053085563484575703) 10240000000000000000),
            (exactRationalLiteral (103850860605245759) 1600000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-277804460466121114133) 1638400000000000000000),
            (exactRationalLiteral (4858029095944351019) 51200000000000000000),
            (exactRationalLiteral (-10294728599152923) 320000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8533676949283801711) 2457600000000000000000),
            (exactRationalLiteral (-132884395579376853) 25600000000000000000),
            (exactRationalLiteral (3384215964967721) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-16982203990389349537) 655360000000000000000),
            (exactRationalLiteral (208599982360074763) 102400000000000000000),
            (exactRationalLiteral (40126429011847017) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-288682821091390792121) 4915200000000000000000),
            (exactRationalLiteral (3413580955815315213) 51200000000000000000),
            (exactRationalLiteral (-15922768667224957) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (56796156525343369561) 819200000000000000000),
            (exactRationalLiteral (-272438055191280987) 5120000000000000000),
            (exactRationalLiteral (4400869851370839) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (102716965380684691357) 4915200000000000000000),
            (exactRationalLiteral (-31073997829964089) 2048000000000000000),
            (exactRationalLiteral (3961941001854737) 320000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-60642586195817746339) 9830400000000000000000),
            (exactRationalLiteral (79047597554828547) 20480000000000000000),
            (exactRationalLiteral (-10023506316916651) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (130141731641346947) 2457600000000000000000),
            (exactRationalLiteral (94854606023361121) 25600000000000000000),
            (exactRationalLiteral (-3821155172399509) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (10613609923828766187) 1638400000000000000000),
            (exactRationalLiteral (365207265053627883) 51200000000000000000),
            (exactRationalLiteral (5964000765172473) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-43828998844108247) 6553600000000000000),
            (exactRationalLiteral (-129145343462731971) 25600000000000000000),
            (exactRationalLiteral (-2065593022578393) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-151258600562848652713) 9830400000000000000000),
            (exactRationalLiteral (-477425784936583187) 102400000000000000000),
            (exactRationalLiteral (-8333248349840833) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9602748106133104037) 2457600000000000000000),
            (exactRationalLiteral (66557009776104063) 25600000000000000000),
            (exactRationalLiteral (1853178041964269) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (46407880053979210621) 9830400000000000000000),
            (exactRationalLiteral (232390308537573039) 102400000000000000000),
            (exactRationalLiteral (-3932091579710987) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3952992349591718273) 9830400000000000000000),
            (exactRationalLiteral (-46004366840156347) 102400000000000000000),
            (exactRationalLiteral (14275184796452071) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2333587866154300123) 1638400000000000000000),
            (exactRationalLiteral (-80282167349083509) 51200000000000000000),
            (exactRationalLiteral (-29558382215697303) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20697461469953906083) 1228800000000000000000),
            (exactRationalLiteral (-9131742342895997) 2560000000000000000),
            (exactRationalLiteral (27323258493654101) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (604621963607952050633) 9830400000000000000000),
            (exactRationalLiteral (1835963577270717079) 20480000000000000000),
            (exactRationalLiteral (-377187799960005151) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-45191937615356116877) 1228800000000000000000),
            (exactRationalLiteral (-102771362173396479) 512000000000000000),
            (exactRationalLiteral (5851531935314063) 80000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-372748074142113570739) 9830400000000000000000),
            (exactRationalLiteral (15963038263642173023) 102400000000000000000),
            (exactRationalLiteral (69249716323894469) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (27971429456450109079) 983040000000000000000),
            (exactRationalLiteral (-340795727569170403) 10240000000000000000),
            (exactRationalLiteral (-14026114969979873) 320000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (3710615129098238777) 4915200000000000000000),
            (exactRationalLiteral (-285431933007556829) 51200000000000000000),
            (exactRationalLiteral (21956302539042833) 1600000000000000000),
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
          (exactRationalLiteral (579308597760899363) 614400000000000000000),
          (exactRationalLiteral (18093603196302420073) 614400000000000000000),
          (exactRationalLiteral (17515921183136085947) 409600000000000000000),
          (exactRationalLiteral (275023606612890219) 6400000000000000000),
          (exactRationalLiteral (9859173682429074271) 153600000000000000000),
          (exactRationalLiteral (216381478969608531) 12800000000000000000),
          (exactRationalLiteral (35775924928239347) 24576000000000000000),
          (exactRationalLiteral (21077841987731429) 51200000000000000000),
          (exactRationalLiteral (245274863005567177) 51200000000000000000),
          (exactRationalLiteral (51083851807103271) 12800000000000000000),
          (exactRationalLiteral (95447713265334839) 6144000000000000000),
          (exactRationalLiteral (262961066499472217) 38400000000000000000),
          (exactRationalLiteral (102983114675249351) 15360000000000000000),
          (exactRationalLiteral (6298014823318481) 38400000000000000000),
          (exactRationalLiteral (7732561944746516993) 1228800000000000000000),
          (exactRationalLiteral (13138555742872897103) 614400000000000000000),
          (exactRationalLiteral (21817722378491250881) 307200000000000000000),
          (exactRationalLiteral (2493050497814139237) 40960000000000000000),
          (exactRationalLiteral (31904441587050080389) 1228800000000000000000),
          (exactRationalLiteral (139410064954944241) 38400000000000000000),
          (exactRationalLiteral (106017866482078880333) 614400000000000000000),
          (exactRationalLiteral (225482889207535851853) 614400000000000000000),
          (exactRationalLiteral (106017866482078880333) 614400000000000000000),
          (exactRationalLiteral (139410064954944241) 38400000000000000000),
          (exactRationalLiteral (31904441587050080389) 1228800000000000000000),
          (exactRationalLiteral (2493050497814139237) 40960000000000000000),
          (exactRationalLiteral (21817722378491250881) 307200000000000000000),
          (exactRationalLiteral (13138555742872897103) 614400000000000000000),
          (exactRationalLiteral (7732561944746516993) 1228800000000000000000),
          (exactRationalLiteral (6298014823318481) 38400000000000000000),
          (exactRationalLiteral (102983114675249351) 15360000000000000000),
          (exactRationalLiteral (262961066499472217) 38400000000000000000),
          (exactRationalLiteral (95447713265334839) 6144000000000000000),
          (exactRationalLiteral (51083851807103271) 12800000000000000000),
          (exactRationalLiteral (245274863005567177) 51200000000000000000),
          (exactRationalLiteral (21077841987731429) 51200000000000000000),
          (exactRationalLiteral (35775924928239347) 24576000000000000000),
          (exactRationalLiteral (216381478969608531) 12800000000000000000),
          (exactRationalLiteral (9859173682429074271) 153600000000000000000),
          (exactRationalLiteral (275023606612890219) 6400000000000000000),
          (exactRationalLiteral (17515921183136085947) 409600000000000000000),
          (exactRationalLiteral (18093603196302420073) 614400000000000000000),
          (exactRationalLiteral (579308597760899363) 614400000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 54),
      (28, 6)
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
            (exactRationalLiteral (2247987590728154671) 4915200000000000000000),
            (exactRationalLiteral (-204362508248014061) 51200000000000000000),
            (exactRationalLiteral (18578409840728551) 1600000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (128870635763528983013) 4915200000000000000000),
            (exactRationalLiteral (-1945037333969278431) 51200000000000000000),
            (exactRationalLiteral (-50398773211813843) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-92172499691597516119) 3276800000000000000000),
            (exactRationalLiteral (16050711573728376207) 102400000000000000000),
            (exactRationalLiteral (-25413061280792877) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2407867015519879459) 49152000000000000000),
            (exactRationalLiteral (-2422316097003751479) 12800000000000000000),
            (exactRationalLiteral (44226318989009933) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (218277570597725732341) 3276800000000000000000),
            (exactRationalLiteral (7500113919825412707) 102400000000000000000),
            (exactRationalLiteral (-462664183304081193) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-275014750812718751) 16384000000000000000),
            (exactRationalLiteral (72348485941651647) 12800000000000000000),
            (exactRationalLiteral (6336068066882343) 80000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (49170958028012387) 39321600000000000000),
            (exactRationalLiteral (-207515823351114373) 51200000000000000000),
            (exactRationalLiteral (-34058445785318129) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4047842460448057639) 9830400000000000000000),
            (exactRationalLiteral (16033308659238869) 102400000000000000000),
            (exactRationalLiteral (16743652953245537) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (47751188743976926667) 9830400000000000000000),
            (exactRationalLiteral (214737911083133919) 102400000000000000000),
            (exactRationalLiteral (-4894107147508573) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2005059064061090327) 491520000000000000000),
            (exactRationalLiteral (14890646290007427) 5120000000000000000),
            (exactRationalLiteral (2094932795002267) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-51408954249096260949) 3276800000000000000000),
            (exactRationalLiteral (-512613025647217027) 102400000000000000000),
            (exactRationalLiteral (-9260372005476087) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3447108156669102107) 491520000000000000000),
            (exactRationalLiteral (-137411235431838227) 25600000000000000000),
            (exactRationalLiteral (-413470592394947) 160000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (34105666388086877063) 4915200000000000000000),
            (exactRationalLiteral (390075776662688539) 51200000000000000000),
            (exactRationalLiteral (1294051007871571) 320000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (652062421697927573) 2457600000000000000000),
            (exactRationalLiteral (78893443326367089) 25600000000000000000),
            (exactRationalLiteral (-4159426176097507) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-11674888261185239633) 1966080000000000000000),
            (exactRationalLiteral (363643482031321919) 102400000000000000000),
            (exactRationalLiteral (-5773746554493757) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (98281569286114500331) 4915200000000000000000),
            (exactRationalLiteral (-703617565805438433) 51200000000000000000),
            (exactRationalLiteral (16806484962558211) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (162473575501292961613) 2457600000000000000000),
            (exactRationalLiteral (-255415036793894411) 5120000000000000000),
            (exactRationalLiteral (4110639347322449) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-89709155828573209221) 1638400000000000000000),
            (exactRationalLiteral (3109742577877201373) 51200000000000000000),
            (exactRationalLiteral (-14461069126586427) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-253023525369411895721) 9830400000000000000000),
            (exactRationalLiteral (357314420470330107) 102400000000000000000),
            (exactRationalLiteral (6846158008656131) 640000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9290906083095668713) 2457600000000000000000),
            (exactRationalLiteral (-119614207677115237) 25600000000000000000),
            (exactRationalLiteral (3250877986163087) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-804874552607067584761) 4915200000000000000000),
            (exactRationalLiteral (4656303489750706011) 51200000000000000000),
            (exactRationalLiteral (-49389160101057889) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1712390161126554153089) 4915200000000000000000),
            (exactRationalLiteral (-1971672423655842823) 10240000000000000000),
            (exactRationalLiteral (99681988966586441) 1600000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-804874552607067584761) 4915200000000000000000),
            (exactRationalLiteral (4656303489750706011) 51200000000000000000),
            (exactRationalLiteral (-49389160101057889) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-9290906083095668713) 2457600000000000000000),
            (exactRationalLiteral (-119614207677115237) 25600000000000000000),
            (exactRationalLiteral (3250877986163087) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-253023525369411895721) 9830400000000000000000),
            (exactRationalLiteral (357314420470330107) 102400000000000000000),
            (exactRationalLiteral (6846158008656131) 640000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-89709155828573209221) 1638400000000000000000),
            (exactRationalLiteral (3109742577877201373) 51200000000000000000),
            (exactRationalLiteral (-14461069126586427) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (162473575501292961613) 2457600000000000000000),
            (exactRationalLiteral (-255415036793894411) 5120000000000000000),
            (exactRationalLiteral (4110639347322449) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (98281569286114500331) 4915200000000000000000),
            (exactRationalLiteral (-703617565805438433) 51200000000000000000),
            (exactRationalLiteral (16806484962558211) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-11674888261185239633) 1966080000000000000000),
            (exactRationalLiteral (363643482031321919) 102400000000000000000),
            (exactRationalLiteral (-5773746554493757) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (652062421697927573) 2457600000000000000000),
            (exactRationalLiteral (78893443326367089) 25600000000000000000),
            (exactRationalLiteral (-4159426176097507) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (34105666388086877063) 4915200000000000000000),
            (exactRationalLiteral (390075776662688539) 51200000000000000000),
            (exactRationalLiteral (1294051007871571) 320000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3447108156669102107) 491520000000000000000),
            (exactRationalLiteral (-137411235431838227) 25600000000000000000),
            (exactRationalLiteral (-413470592394947) 160000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-51408954249096260949) 3276800000000000000000),
            (exactRationalLiteral (-512613025647217027) 102400000000000000000),
            (exactRationalLiteral (-9260372005476087) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2005059064061090327) 491520000000000000000),
            (exactRationalLiteral (14890646290007427) 5120000000000000000),
            (exactRationalLiteral (2094932795002267) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (47751188743976926667) 9830400000000000000000),
            (exactRationalLiteral (214737911083133919) 102400000000000000000),
            (exactRationalLiteral (-4894107147508573) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4047842460448057639) 9830400000000000000000),
            (exactRationalLiteral (16033308659238869) 102400000000000000000),
            (exactRationalLiteral (16743652953245537) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (49170958028012387) 39321600000000000000),
            (exactRationalLiteral (-207515823351114373) 51200000000000000000),
            (exactRationalLiteral (-34058445785318129) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-275014750812718751) 16384000000000000000),
            (exactRationalLiteral (72348485941651647) 12800000000000000000),
            (exactRationalLiteral (6336068066882343) 80000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (218277570597725732341) 3276800000000000000000),
            (exactRationalLiteral (7500113919825412707) 102400000000000000000),
            (exactRationalLiteral (-462664183304081193) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2407867015519879459) 49152000000000000000),
            (exactRationalLiteral (-2422316097003751479) 12800000000000000000),
            (exactRationalLiteral (44226318989009933) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-92172499691597516119) 3276800000000000000000),
            (exactRationalLiteral (16050711573728376207) 102400000000000000000),
            (exactRationalLiteral (-25413061280792877) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (128870635763528983013) 4915200000000000000000),
            (exactRationalLiteral (-1945037333969278431) 51200000000000000000),
            (exactRationalLiteral (-50398773211813843) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2247987590728154671) 4915200000000000000000),
            (exactRationalLiteral (-204362508248014061) 51200000000000000000),
            (exactRationalLiteral (18578409840728551) 1600000000000000000),
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
          (exactRationalLiteral (8415432549048123913) 153600000000000000000),
          (exactRationalLiteral (84487790351383644193) 1228800000000000000000),
          (exactRationalLiteral (324223270135875077) 19200000000000000000),
          (exactRationalLiteral (20840599743699211) 15360000000000000000),
          (exactRationalLiteral (42493595708147347) 102400000000000000000),
          (exactRationalLiteral (6047529893499987989) 1228800000000000000000),
          (exactRationalLiteral (256376517260427221) 61440000000000000000),
          (exactRationalLiteral (19474118312759334977) 1228800000000000000000),
          (exactRationalLiteral (735582392854026983) 102400000000000000000),
          (exactRationalLiteral (1470648233763754539) 204800000000000000000),
          (exactRationalLiteral (21902383441172183) 61440000000000000000),
          (exactRationalLiteral (185890055848640177) 30720000000000000000),
          (exactRationalLiteral (12555542881055231) 614400000000000000),
          (exactRationalLiteral (2599487284682364617) 38400000000000000000),
          (exactRationalLiteral (4354332273517212883) 76800000000000000000),
          (exactRationalLiteral (3968591069393886889) 153600000000000000000),
          (exactRationalLiteral (241001568528948187) 61440000000000000000),
          (exactRationalLiteral (12796760512469847341) 76800000000000000000),
          (exactRationalLiteral (27222912154439232569) 76800000000000000000),
          (exactRationalLiteral (12796760512469847341) 76800000000000000000),
          (exactRationalLiteral (241001568528948187) 61440000000000000000),
          (exactRationalLiteral (3968591069393886889) 153600000000000000000),
          (exactRationalLiteral (4354332273517212883) 76800000000000000000),
          (exactRationalLiteral (2599487284682364617) 38400000000000000000),
          (exactRationalLiteral (12555542881055231) 614400000000000000),
          (exactRationalLiteral (185890055848640177) 30720000000000000000),
          (exactRationalLiteral (21902383441172183) 61440000000000000000),
          (exactRationalLiteral (1470648233763754539) 204800000000000000000),
          (exactRationalLiteral (735582392854026983) 102400000000000000000),
          (exactRationalLiteral (19474118312759334977) 1228800000000000000000),
          (exactRationalLiteral (256376517260427221) 61440000000000000000),
          (exactRationalLiteral (6047529893499987989) 1228800000000000000000),
          (exactRationalLiteral (42493595708147347) 102400000000000000000),
          (exactRationalLiteral (20840599743699211) 15360000000000000000),
          (exactRationalLiteral (324223270135875077) 19200000000000000000),
          (exactRationalLiteral (84487790351383644193) 1228800000000000000000),
          (exactRationalLiteral (8415432549048123913) 153600000000000000000),
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
      (27, 53),
      (28, 5)
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
            (exactRationalLiteral (410413962845185263) 1638400000000000000000),
            (exactRationalLiteral (-136804654281728421) 51200000000000000000),
            (exactRationalLiteral (15200517142414269) 1600000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (116674553687723888399) 4915200000000000000000),
            (exactRationalLiteral (-2107168823540362759) 51200000000000000000),
            (exactRationalLiteral (-30666971573728321) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-180896837478210555023) 9830400000000000000000),
            (exactRationalLiteral (15759733773395830007) 102400000000000000000),
            (exactRationalLiteral (-120075838885480223) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-24713327168300539227) 409600000000000000000),
            (exactRationalLiteral (-2215473502422832511) 12800000000000000000),
            (exactRationalLiteral (59194978301449551) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (693939519579104394781) 9830400000000000000000),
            (exactRationalLiteral (5478504419920935851) 102400000000000000000),
            (exactRationalLiteral (-109628113329631447) 640000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19794422983928025407) 1228800000000000000000),
            (exactRationalLiteral (41556802192162747) 2560000000000000000),
            (exactRationalLiteral (36037422175169329) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (894914641938512257) 983040000000000000000),
            (exactRationalLiteral (-352749733631628541) 51200000000000000000),
            (exactRationalLiteral (-7711701870987791) 320000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1246948300142168039) 3276800000000000000000),
            (exactRationalLiteral (87944856785807949) 102400000000000000000),
            (exactRationalLiteral (19212121110039003) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (16325679620811478987) 3276800000000000000000),
            (exactRationalLiteral (38647490271500891) 20480000000000000000),
            (exactRationalLiteral (-5856122715306159) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3499373640519284547) 819200000000000000000),
            (exactRationalLiteral (83316472136122199) 25600000000000000000),
            (exactRationalLiteral (467337509608053) 160000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-157417373859860339069) 9830400000000000000000),
            (exactRationalLiteral (-551508760980391883) 102400000000000000000),
            (exactRationalLiteral (-10187495661111341) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3616964694247564417) 491520000000000000000),
            (exactRationalLiteral (-145684167158529851) 25600000000000000000),
            (exactRationalLiteral (-2069112901371077) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (7305157825126408817) 983040000000000000000),
            (exactRationalLiteral (416969305368490723) 51200000000000000000),
            (exactRationalLiteral (6976509313543237) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1074156883528168031) 2457600000000000000000),
            (exactRationalLiteral (12315839322916213) 5120000000000000000),
            (exactRationalLiteral (-899539435959101) 160000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-56244866333342500159) 9830400000000000000000),
            (exactRationalLiteral (349048015338192679) 102400000000000000000),
            (exactRationalLiteral (-1523986792070863) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (94249528830645706369) 4915200000000000000000),
            (exactRationalLiteral (-642398066048636537) 51200000000000000000),
            (exactRationalLiteral (13803264915842737) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (155051958148234508423) 2457600000000000000000),
            (exactRationalLiteral (-47910588082540279) 1024000000000000000),
            (exactRationalLiteral (3820408843274059) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-50261488435047766889) 983040000000000000000),
            (exactRationalLiteral (2835138190751858133) 51200000000000000000),
            (exactRationalLiteral (-12999369585947897) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-250492451921944812667) 9830400000000000000000),
            (exactRationalLiteral (482446302706320003) 102400000000000000000),
            (exactRationalLiteral (28335151074714293) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9970114145239621627) 2457600000000000000000),
            (exactRationalLiteral (-106877371690072157) 25600000000000000000),
            (exactRationalLiteral (3117540007358453) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-777521063658197216459) 4915200000000000000000),
            (exactRationalLiteral (4462915815135887907) 51200000000000000000),
            (exactRationalLiteral (-47304677206351163) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1654419496797923268419) 4915200000000000000000),
            (exactRationalLiteral (-9467971905690186987) 51200000000000000000),
            (exactRationalLiteral (95513117327927123) 1600000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-777521063658197216459) 4915200000000000000000),
            (exactRationalLiteral (4462915815135887907) 51200000000000000000),
            (exactRationalLiteral (-47304677206351163) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-9970114145239621627) 2457600000000000000000),
            (exactRationalLiteral (-106877371690072157) 25600000000000000000),
            (exactRationalLiteral (3117540007358453) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-250492451921944812667) 9830400000000000000000),
            (exactRationalLiteral (482446302706320003) 102400000000000000000),
            (exactRationalLiteral (28335151074714293) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-50261488435047766889) 983040000000000000000),
            (exactRationalLiteral (2835138190751858133) 51200000000000000000),
            (exactRationalLiteral (-12999369585947897) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (155051958148234508423) 2457600000000000000000),
            (exactRationalLiteral (-47910588082540279) 1024000000000000000),
            (exactRationalLiteral (3820408843274059) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (94249528830645706369) 4915200000000000000000),
            (exactRationalLiteral (-642398066048636537) 51200000000000000000),
            (exactRationalLiteral (13803264915842737) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-56244866333342500159) 9830400000000000000000),
            (exactRationalLiteral (349048015338192679) 102400000000000000000),
            (exactRationalLiteral (-1523986792070863) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1074156883528168031) 2457600000000000000000),
            (exactRationalLiteral (12315839322916213) 5120000000000000000),
            (exactRationalLiteral (-899539435959101) 160000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (7305157825126408817) 983040000000000000000),
            (exactRationalLiteral (416969305368490723) 51200000000000000000),
            (exactRationalLiteral (6976509313543237) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3616964694247564417) 491520000000000000000),
            (exactRationalLiteral (-145684167158529851) 25600000000000000000),
            (exactRationalLiteral (-2069112901371077) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-157417373859860339069) 9830400000000000000000),
            (exactRationalLiteral (-551508760980391883) 102400000000000000000),
            (exactRationalLiteral (-10187495661111341) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3499373640519284547) 819200000000000000000),
            (exactRationalLiteral (83316472136122199) 25600000000000000000),
            (exactRationalLiteral (467337509608053) 160000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (16325679620811478987) 3276800000000000000000),
            (exactRationalLiteral (38647490271500891) 20480000000000000000),
            (exactRationalLiteral (-5856122715306159) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1246948300142168039) 3276800000000000000000),
            (exactRationalLiteral (87944856785807949) 102400000000000000000),
            (exactRationalLiteral (19212121110039003) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (894914641938512257) 983040000000000000000),
            (exactRationalLiteral (-352749733631628541) 51200000000000000000),
            (exactRationalLiteral (-7711701870987791) 320000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-19794422983928025407) 1228800000000000000000),
            (exactRationalLiteral (41556802192162747) 2560000000000000000),
            (exactRationalLiteral (36037422175169329) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (693939519579104394781) 9830400000000000000000),
            (exactRationalLiteral (5478504419920935851) 102400000000000000000),
            (exactRationalLiteral (-109628113329631447) 640000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-24713327168300539227) 409600000000000000000),
            (exactRationalLiteral (-2215473502422832511) 12800000000000000000),
            (exactRationalLiteral (59194978301449551) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-180896837478210555023) 9830400000000000000000),
            (exactRationalLiteral (15759733773395830007) 102400000000000000000),
            (exactRationalLiteral (-120075838885480223) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (116674553687723888399) 4915200000000000000000),
            (exactRationalLiteral (-2107168823540362759) 51200000000000000000),
            (exactRationalLiteral (-30666971573728321) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (410413962845185263) 1638400000000000000000),
            (exactRationalLiteral (-136804654281728421) 51200000000000000000),
            (exactRationalLiteral (15200517142414269) 1600000000000000000),
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
          (exactRationalLiteral (1688946349157141) 4915200000000000000),
          (exactRationalLiteral (15361774167850593619) 614400000000000000000),
          (exactRationalLiteral (5712223373156303551) 245760000000000000000),
          (exactRationalLiteral (9839029876417181) 150000000000000000),
          (exactRationalLiteral (461385333950033003) 6400000000000000000),
          (exactRationalLiteral (2538980161400667179) 153600000000000000000),
          (exactRationalLiteral (225808204762810019) 204800000000000000000),
          (exactRationalLiteral (493534667691525961) 1228800000000000000000),
          (exactRationalLiteral (96755277032377213) 19200000000000000000),
          (exactRationalLiteral (10503126248034043) 2400000000000000000),
          (exactRationalLiteral (103582634239331163) 6400000000000000000),
          (exactRationalLiteral (3618766443630317) 480000000000000000),
          (exactRationalLiteral (73823983782842263) 9600000000000000000),
          (exactRationalLiteral (2432094231114601) 4800000000000000000),
          (exactRationalLiteral (7162338402451812779) 1228800000000000000000),
          (exactRationalLiteral (12027454304195312741) 614400000000000000000),
          (exactRationalLiteral (6612636831805594217) 102400000000000000000),
          (exactRationalLiteral (32501437692516902953) 614400000000000000000),
          (exactRationalLiteral (10493826564889806109) 409600000000000000000),
          (exactRationalLiteral (20080977166556963) 4800000000000000000),
          (exactRationalLiteral (32960531974027970293) 204800000000000000000),
          (exactRationalLiteral (210389004537849617551) 614400000000000000000),
          (exactRationalLiteral (32960531974027970293) 204800000000000000000),
          (exactRationalLiteral (20080977166556963) 4800000000000000000),
          (exactRationalLiteral (10493826564889806109) 409600000000000000000),
          (exactRationalLiteral (32501437692516902953) 614400000000000000000),
          (exactRationalLiteral (6612636831805594217) 102400000000000000000),
          (exactRationalLiteral (12027454304195312741) 614400000000000000000),
          (exactRationalLiteral (7162338402451812779) 1228800000000000000000),
          (exactRationalLiteral (2432094231114601) 4800000000000000000),
          (exactRationalLiteral (73823983782842263) 9600000000000000000),
          (exactRationalLiteral (3618766443630317) 480000000000000000),
          (exactRationalLiteral (103582634239331163) 6400000000000000000),
          (exactRationalLiteral (10503126248034043) 2400000000000000000),
          (exactRationalLiteral (96755277032377213) 19200000000000000000),
          (exactRationalLiteral (493534667691525961) 1228800000000000000000),
          (exactRationalLiteral (225808204762810019) 204800000000000000000),
          (exactRationalLiteral (2538980161400667179) 153600000000000000000),
          (exactRationalLiteral (461385333950033003) 6400000000000000000),
          (exactRationalLiteral (9839029876417181) 150000000000000000),
          (exactRationalLiteral (5712223373156303551) 245760000000000000000),
          (exactRationalLiteral (15361774167850593619) 614400000000000000000),
          (exactRationalLiteral (1688946349157141) 4915200000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 52),
      (28, 4)
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
            (exactRationalLiteral (579308597760899363) 4915200000000000000000),
            (exactRationalLiteral (-82758371108699909) 51200000000000000000),
            (exactRationalLiteral (11822624444099987) 1600000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (103742464294149314081) 4915200000000000000000),
            (exactRationalLiteral (-2190373106559104999) 51200000000000000000),
            (exactRationalLiteral (-10935169935642799) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-88157996014880087041) 9830400000000000000000),
            (exactRationalLiteral (15090104862644534423) 102400000000000000000),
            (exactRationalLiteral (-214738616490167569) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-86662608142571459663) 1228800000000000000000),
            (exactRationalLiteral (-1948756270592155071) 12800000000000000000),
            (exactRationalLiteral (74163637613889169) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (719890953765475818899) 9830400000000000000000),
            (exactRationalLiteral (3114989386640154827) 102400000000000000000),
            (exactRationalLiteral (-633616949992233277) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-18097841524698080593) 1228800000000000000000),
            (exactRationalLiteral (360647863343006279) 12800000000000000000),
            (exactRationalLiteral (40394504015926943) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (25031632551533857) 65536000000000000000),
            (exactRationalLiteral (-515983898190626013) 51200000000000000000),
            (exactRationalLiteral (-43058572924559781) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2972756433764014523) 9830400000000000000000),
            (exactRationalLiteral (169730277539550893) 102400000000000000000),
            (exactRationalLiteral (21680589266832469) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (50062342035724599439) 9830400000000000000000),
            (exactRationalLiteral (167888929360684647) 102400000000000000000),
            (exactRationalLiteral (-1363627656620749) 640000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (11027027023963222007) 2457600000000000000000),
            (exactRationalLiteral (18629346366871851) 5120000000000000000),
            (exactRationalLiteral (2578442301078263) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-6434095394731942699) 393216000000000000000),
            (exactRationalLiteral (-118822598187221551) 20480000000000000000),
            (exactRationalLiteral (-2222923863349319) 640000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6327921622921013161) 819200000000000000000),
            (exactRationalLiteral (-153964138642806843) 25600000000000000000),
            (exactRationalLiteral (-2070872840767419) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (2607556539113483253) 327680000000000000000),
            (exactRationalLiteral (89177570234206887) 10240000000000000000),
            (exactRationalLiteral (7482763587728619) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1388306613043316369) 2457600000000000000000),
            (exactRationalLiteral (42911865888003049) 25600000000000000000),
            (exactRationalLiteral (-4835968183493503) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-10830373408753700573) 1966080000000000000000),
            (exactRationalLiteral (70290317538951003) 20480000000000000000),
            (exactRationalLiteral (2725772970352031) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (18109753346631427619) 983040000000000000000),
            (exactRationalLiteral (-593191446478696537) 51200000000000000000),
            (exactRationalLiteral (10800044869127263) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (49362929952122980771) 819200000000000000000),
            (exactRationalLiteral (-224851766047701939) 5120000000000000000),
            (exactRationalLiteral (3530178339225669) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-235047341215071788867) 4915200000000000000000),
            (exactRationalLiteral (2589767794439285493) 51200000000000000000),
            (exactRationalLiteral (-11537670045309367) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-82427111616228195527) 3276800000000000000000),
            (exactRationalLiteral (583995629068044451) 102400000000000000000),
            (exactRationalLiteral (22439512106147931) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-10574501247206971669) 2457600000000000000000),
            (exactRationalLiteral (-94673887618247613) 25600000000000000000),
            (exactRationalLiteral (2984202028553819) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-250434295654093092023) 1638400000000000000000),
            (exactRationalLiteral (4277866072099896707) 51200000000000000000),
            (exactRationalLiteral (-45220194311644437) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1598741147285162634701) 4915200000000000000000),
            (exactRationalLiteral (-9094257179655797131) 51200000000000000000),
            (exactRationalLiteral (18268849137853561) 320000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-250434295654093092023) 1638400000000000000000),
            (exactRationalLiteral (4277866072099896707) 51200000000000000000),
            (exactRationalLiteral (-45220194311644437) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-10574501247206971669) 2457600000000000000000),
            (exactRationalLiteral (-94673887618247613) 25600000000000000000),
            (exactRationalLiteral (2984202028553819) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-82427111616228195527) 3276800000000000000000),
            (exactRationalLiteral (583995629068044451) 102400000000000000000),
            (exactRationalLiteral (22439512106147931) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-235047341215071788867) 4915200000000000000000),
            (exactRationalLiteral (2589767794439285493) 51200000000000000000),
            (exactRationalLiteral (-11537670045309367) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (49362929952122980771) 819200000000000000000),
            (exactRationalLiteral (-224851766047701939) 5120000000000000000),
            (exactRationalLiteral (3530178339225669) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (18109753346631427619) 983040000000000000000),
            (exactRationalLiteral (-593191446478696537) 51200000000000000000),
            (exactRationalLiteral (10800044869127263) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-10830373408753700573) 1966080000000000000000),
            (exactRationalLiteral (70290317538951003) 20480000000000000000),
            (exactRationalLiteral (2725772970352031) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1388306613043316369) 2457600000000000000000),
            (exactRationalLiteral (42911865888003049) 25600000000000000000),
            (exactRationalLiteral (-4835968183493503) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (2607556539113483253) 327680000000000000000),
            (exactRationalLiteral (89177570234206887) 10240000000000000000),
            (exactRationalLiteral (7482763587728619) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6327921622921013161) 819200000000000000000),
            (exactRationalLiteral (-153964138642806843) 25600000000000000000),
            (exactRationalLiteral (-2070872840767419) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-6434095394731942699) 393216000000000000000),
            (exactRationalLiteral (-118822598187221551) 20480000000000000000),
            (exactRationalLiteral (-2222923863349319) 640000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (11027027023963222007) 2457600000000000000000),
            (exactRationalLiteral (18629346366871851) 5120000000000000000),
            (exactRationalLiteral (2578442301078263) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (50062342035724599439) 9830400000000000000000),
            (exactRationalLiteral (167888929360684647) 102400000000000000000),
            (exactRationalLiteral (-1363627656620749) 640000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2972756433764014523) 9830400000000000000000),
            (exactRationalLiteral (169730277539550893) 102400000000000000000),
            (exactRationalLiteral (21680589266832469) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (25031632551533857) 65536000000000000000),
            (exactRationalLiteral (-515983898190626013) 51200000000000000000),
            (exactRationalLiteral (-43058572924559781) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-18097841524698080593) 1228800000000000000000),
            (exactRationalLiteral (360647863343006279) 12800000000000000000),
            (exactRationalLiteral (40394504015926943) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (719890953765475818899) 9830400000000000000000),
            (exactRationalLiteral (3114989386640154827) 102400000000000000000),
            (exactRationalLiteral (-633616949992233277) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-86662608142571459663) 1228800000000000000000),
            (exactRationalLiteral (-1948756270592155071) 12800000000000000000),
            (exactRationalLiteral (74163637613889169) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-88157996014880087041) 9830400000000000000000),
            (exactRationalLiteral (15090104862644534423) 102400000000000000000),
            (exactRationalLiteral (-214738616490167569) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (103742464294149314081) 4915200000000000000000),
            (exactRationalLiteral (-2190373106559104999) 51200000000000000000),
            (exactRationalLiteral (-10935169935642799) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (579308597760899363) 4915200000000000000000),
            (exactRationalLiteral (-82758371108699909) 51200000000000000000),
            (exactRationalLiteral (11822624444099987) 1600000000000000000),
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
          (exactRationalLiteral (768990847598750313) 10240000000000000000),
          (exactRationalLiteral (90911541610468443191) 1228800000000000000000),
          (exactRationalLiteral (12409362072656053) 800000000000000000),
          (exactRationalLiteral (6442184470601657) 9600000000000000000),
          (exactRationalLiteral (6676054165352669) 19200000000000000000),
          (exactRationalLiteral (2106044725048893473) 409600000000000000000),
          (exactRationalLiteral (94286028531217113) 20480000000000000000),
          (exactRationalLiteral (20333566407610618519) 1228800000000000000000),
          (exactRationalLiteral (486296769579586511) 61440000000000000000),
          (exactRationalLiteral (5059214132264453831) 614400000000000000000),
          (exactRationalLiteral (187795646331874501) 307200000000000000000),
          (exactRationalLiteral (107812830796529147) 19200000000000000000),
          (exactRationalLiteral (180395005502390561) 9600000000000000000),
          (exactRationalLiteral (295928212106314409) 4800000000000000000),
          (exactRationalLiteral (158198804621042241) 3200000000000000000),
          (exactRationalLiteral (97251193507846091) 3840000000000000000),
          (exactRationalLiteral (1356204621620681921) 307200000000000000000),
          (exactRationalLiteral (1492721070318283697) 9600000000000000000),
          (exactRationalLiteral (3176367257806674139) 9600000000000000000),
          (exactRationalLiteral (1492721070318283697) 9600000000000000000),
          (exactRationalLiteral (1356204621620681921) 307200000000000000000),
          (exactRationalLiteral (97251193507846091) 3840000000000000000),
          (exactRationalLiteral (158198804621042241) 3200000000000000000),
          (exactRationalLiteral (295928212106314409) 4800000000000000000),
          (exactRationalLiteral (180395005502390561) 9600000000000000000),
          (exactRationalLiteral (107812830796529147) 19200000000000000000),
          (exactRationalLiteral (187795646331874501) 307200000000000000000),
          (exactRationalLiteral (5059214132264453831) 614400000000000000000),
          (exactRationalLiteral (486296769579586511) 61440000000000000000),
          (exactRationalLiteral (20333566407610618519) 1228800000000000000000),
          (exactRationalLiteral (94286028531217113) 20480000000000000000),
          (exactRationalLiteral (2106044725048893473) 409600000000000000000),
          (exactRationalLiteral (6676054165352669) 19200000000000000000),
          (exactRationalLiteral (6442184470601657) 9600000000000000000),
          (exactRationalLiteral (12409362072656053) 800000000000000000),
          (exactRationalLiteral (90911541610468443191) 1228800000000000000000),
          (exactRationalLiteral (768990847598750313) 10240000000000000000),
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
      (27, 51),
      (28, 3)
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
            (exactRationalLiteral (1688946349157141) 39321600000000000000),
            (exactRationalLiteral (-1688946349157141) 2048000000000000000),
            (exactRationalLiteral (1688946349157141) 320000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (90547930822119312587) 4915200000000000000000),
            (exactRationalLiteral (-2194650183025505151) 51200000000000000000),
            (exactRationalLiteral (8796631702442723) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-38192089820909381) 655360000000000000000),
            (exactRationalLiteral (2808364968294897891) 20480000000000000000),
            (exactRationalLiteral (-61880278818970983) 640000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-97405307477507961589) 1228800000000000000000),
            (exactRationalLiteral (-1622164401511719159) 12800000000000000000),
            (exactRationalLiteral (89132296926328787) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (243545193717344548123) 3276800000000000000000),
            (exactRationalLiteral (81913763996613927) 20480000000000000000),
            (exactRationalLiteral (-719093333336309319) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5143930656361963049) 409600000000000000000),
            (exactRationalLiteral (530940043088229279) 12800000000000000000),
            (exactRationalLiteral (44751585856684557) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1753234077151917479) 4915200000000000000000),
            (exactRationalLiteral (-697218317028106789) 51200000000000000000),
            (exactRationalLiteral (-47558636494180607) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1684333824697545673) 9830400000000000000000),
            (exactRationalLiteral (261389570920467701) 102400000000000000000),
            (exactRationalLiteral (4829811484725187) 640000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (50984009890220272037) 9830400000000000000000),
            (exactRationalLiteral (27738469018534899) 20480000000000000000),
            (exactRationalLiteral (-7780153850901331) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2323563148318893737) 491520000000000000000),
            (exactRationalLiteral (103944010544748303) 25600000000000000000),
            (exactRationalLiteral (2820197054116261) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-54851382246779571387) 3276800000000000000000),
            (exactRationalLiteral (-640425715514364643) 102400000000000000000),
            (exactRationalLiteral (-12041742972381849) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-19932407214466674937) 2457600000000000000000),
            (exactRationalLiteral (-162251149884669203) 25600000000000000000),
            (exactRationalLiteral (-2072632780163761) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (41880493373877940361) 4915200000000000000000),
            (exactRationalLiteral (19073256562812787) 2048000000000000000),
            (exactRationalLiteral (7989017861914001) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (317278621230924127) 491520000000000000000),
            (exactRationalLiteral (22891451146633041) 25600000000000000000),
            (exactRationalLiteral (-5174239187191501) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-51993449202906056827) 9830400000000000000000),
            (exactRationalLiteral (370854199101008927) 102400000000000000000),
            (exactRationalLiteral (279021309310997) 128000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (87107205712527624133) 4915200000000000000000),
            (exactRationalLiteral (-555997707095618433) 51200000000000000000),
            (exactRationalLiteral (7796824822411789) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (141549242965210456483) 2457600000000000000000),
            (exactRationalLiteral (-211311513698896043) 5120000000000000000),
            (exactRationalLiteral (3239947835177279) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-73390586886780622443) 1638400000000000000000),
            (exactRationalLiteral (2373631388939483453) 51200000000000000000),
            (exactRationalLiteral (-10075970504670837) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-243531669484876810151) 9830400000000000000000),
            (exactRationalLiteral (661962399555503451) 102400000000000000000),
            (exactRationalLiteral (16543873137581569) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2221453500097806011) 491520000000000000000),
            (exactRationalLiteral (-16600751092328321) 5120000000000000000),
            (exactRationalLiteral (570172809949837) 160000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-726169994929840802167) 4915200000000000000000),
            (exactRationalLiteral (4101154260642732411) 51200000000000000000),
            (exactRationalLiteral (-43135711416937711) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1545255059668944428303) 4915200000000000000000),
            (exactRationalLiteral (-8737217940176044547) 51200000000000000000),
            (exactRationalLiteral (87175374050608487) 1600000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-726169994929840802167) 4915200000000000000000),
            (exactRationalLiteral (4101154260642732411) 51200000000000000000),
            (exactRationalLiteral (-43135711416937711) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2221453500097806011) 491520000000000000000),
            (exactRationalLiteral (-16600751092328321) 5120000000000000000),
            (exactRationalLiteral (570172809949837) 160000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-243531669484876810151) 9830400000000000000000),
            (exactRationalLiteral (661962399555503451) 102400000000000000000),
            (exactRationalLiteral (16543873137581569) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-73390586886780622443) 1638400000000000000000),
            (exactRationalLiteral (2373631388939483453) 51200000000000000000),
            (exactRationalLiteral (-10075970504670837) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (141549242965210456483) 2457600000000000000000),
            (exactRationalLiteral (-211311513698896043) 5120000000000000000),
            (exactRationalLiteral (3239947835177279) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (87107205712527624133) 4915200000000000000000),
            (exactRationalLiteral (-555997707095618433) 51200000000000000000),
            (exactRationalLiteral (7796824822411789) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-51993449202906056827) 9830400000000000000000),
            (exactRationalLiteral (370854199101008927) 102400000000000000000),
            (exactRationalLiteral (279021309310997) 128000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (317278621230924127) 491520000000000000000),
            (exactRationalLiteral (22891451146633041) 25600000000000000000),
            (exactRationalLiteral (-5174239187191501) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (41880493373877940361) 4915200000000000000000),
            (exactRationalLiteral (19073256562812787) 2048000000000000000),
            (exactRationalLiteral (7989017861914001) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-19932407214466674937) 2457600000000000000000),
            (exactRationalLiteral (-162251149884669203) 25600000000000000000),
            (exactRationalLiteral (-2072632780163761) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-54851382246779571387) 3276800000000000000000),
            (exactRationalLiteral (-640425715514364643) 102400000000000000000),
            (exactRationalLiteral (-12041742972381849) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2323563148318893737) 491520000000000000000),
            (exactRationalLiteral (103944010544748303) 25600000000000000000),
            (exactRationalLiteral (2820197054116261) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (50984009890220272037) 9830400000000000000000),
            (exactRationalLiteral (27738469018534899) 20480000000000000000),
            (exactRationalLiteral (-7780153850901331) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1684333824697545673) 9830400000000000000000),
            (exactRationalLiteral (261389570920467701) 102400000000000000000),
            (exactRationalLiteral (4829811484725187) 640000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1753234077151917479) 4915200000000000000000),
            (exactRationalLiteral (-697218317028106789) 51200000000000000000),
            (exactRationalLiteral (-47558636494180607) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5143930656361963049) 409600000000000000000),
            (exactRationalLiteral (530940043088229279) 12800000000000000000),
            (exactRationalLiteral (44751585856684557) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (243545193717344548123) 3276800000000000000000),
            (exactRationalLiteral (81913763996613927) 20480000000000000000),
            (exactRationalLiteral (-719093333336309319) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-97405307477507961589) 1228800000000000000000),
            (exactRationalLiteral (-1622164401511719159) 12800000000000000000),
            (exactRationalLiteral (89132296926328787) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-38192089820909381) 655360000000000000000),
            (exactRationalLiteral (2808364968294897891) 20480000000000000000),
            (exactRationalLiteral (-61880278818970983) 640000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (90547930822119312587) 4915200000000000000000),
            (exactRationalLiteral (-2194650183025505151) 51200000000000000000),
            (exactRationalLiteral (8796631702442723) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1688946349157141) 39321600000000000000),
            (exactRationalLiteral (-1688946349157141) 2048000000000000000),
            (exactRationalLiteral (1688946349157141) 320000000000000000),
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
          (exactRationalLiteral (15200517142414269) 204800000000000000000),
          (exactRationalLiteral (12143550670685514181) 614400000000000000000),
          (exactRationalLiteral (5447403583152416269) 1228800000000000000000),
          (exactRationalLiteral (1593701866587623639) 19200000000000000000),
          (exactRationalLiteral (22868968171782033167) 307200000000000000000),
          (exactRationalLiteral (422313397042522553) 30720000000000000000),
          (exactRationalLiteral (4156057259899573) 5120000000000000000),
          (exactRationalLiteral (99887066636102821) 409600000000000000000),
          (exactRationalLiteral (802754147752526449) 153600000000000000000),
          (exactRationalLiteral (186534831902618459) 38400000000000000000),
          (exactRationalLiteral (2601750198087918301) 153600000000000000000),
          (exactRationalLiteral (851057476767953) 102400000000000000),
          (exactRationalLiteral (45140841455012223) 5120000000000000000),
          (exactRationalLiteral (25615243852048379) 38400000000000000000),
          (exactRationalLiteral (1327180252047299257) 245760000000000000000),
          (exactRationalLiteral (11100011364788134067) 614400000000000000000),
          (exactRationalLiteral (18096030058060209661) 307200000000000000000),
          (exactRationalLiteral (28430931079197747071) 614400000000000000000),
          (exactRationalLiteral (30683122155580786577) 1228800000000000000000),
          (exactRationalLiteral (177309263183032963) 38400000000000000000),
          (exactRationalLiteral (92325488385933395737) 614400000000000000000),
          (exactRationalLiteral (196466290505930464633) 614400000000000000000),
          (exactRationalLiteral (92325488385933395737) 614400000000000000000),
          (exactRationalLiteral (177309263183032963) 38400000000000000000),
          (exactRationalLiteral (30683122155580786577) 1228800000000000000000),
          (exactRationalLiteral (28430931079197747071) 614400000000000000000),
          (exactRationalLiteral (18096030058060209661) 307200000000000000000),
          (exactRationalLiteral (11100011364788134067) 614400000000000000000),
          (exactRationalLiteral (1327180252047299257) 245760000000000000000),
          (exactRationalLiteral (25615243852048379) 38400000000000000000),
          (exactRationalLiteral (45140841455012223) 5120000000000000000),
          (exactRationalLiteral (851057476767953) 102400000000000000),
          (exactRationalLiteral (2601750198087918301) 153600000000000000000),
          (exactRationalLiteral (186534831902618459) 38400000000000000000),
          (exactRationalLiteral (802754147752526449) 153600000000000000000),
          (exactRationalLiteral (99887066636102821) 409600000000000000000),
          (exactRationalLiteral (4156057259899573) 5120000000000000000),
          (exactRationalLiteral (422313397042522553) 30720000000000000000),
          (exactRationalLiteral (22868968171782033167) 307200000000000000000),
          (exactRationalLiteral (1593701866587623639) 19200000000000000000),
          (exactRationalLiteral (5447403583152416269) 1228800000000000000000),
          (exactRationalLiteral (12143550670685514181) 614400000000000000000),
          (exactRationalLiteral (15200517142414269) 204800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 50),
      (28, 2)
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
            (exactRationalLiteral (15200517142414269) 1638400000000000000000),
            (exactRationalLiteral (-15200517142414269) 51200000000000000000),
            (exactRationalLiteral (5066839047471423) 1600000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (15512903302189587289) 983040000000000000000),
            (exactRationalLiteral (-424000010587912643) 10240000000000000000),
            (exactRationalLiteral (5705686668105649) 320000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (79586599861976287651) 9830400000000000000000),
            (exactRationalLiteral (12614893709885695103) 102400000000000000000),
            (exactRationalLiteral (-404064171699542261) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-35336277228737524209) 409600000000000000000),
            (exactRationalLiteral (-49427915807260991) 512000000000000000),
            (exactRationalLiteral (20820191247753681) 80000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (724121968538520046183) 9830400000000000000000),
            (exactRationalLiteral (-105510291202012789) 4096000000000000000),
            (exactRationalLiteral (-804569716680385361) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-11691704352913268333) 1228800000000000000000),
            (exactRationalLiteral (143732110039296547) 2560000000000000000),
            (exactRationalLiteral (49108667697442171) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-6525247871529208801) 4915200000000000000000),
            (exactRationalLiteral (-896452990144070869) 51200000000000000000),
            (exactRationalLiteral (-52058700063801433) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (61222054178648539) 3276800000000000000000),
            (exactRationalLiteral (362922736928558373) 102400000000000000000),
            (exactRationalLiteral (26617525580419401) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (17239651350764770897) 3276800000000000000000),
            (exactRationalLiteral (105647698553473999) 102400000000000000000),
            (exactRationalLiteral (-8742169418698917) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4092096396174835209) 819200000000000000000),
            (exactRationalLiteral (115708308267289343) 25600000000000000000),
            (exactRationalLiteral (3061951807154259) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-168544910443716025223) 9830400000000000000000),
            (exactRationalLiteral (-690446934715162547) 102400000000000000000),
            (exactRationalLiteral (-12968866628017103) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4186158549378848131) 491520000000000000000),
            (exactRationalLiteral (-170545200884116931) 25600000000000000000),
            (exactRationalLiteral (-2074392719560103) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (44839375089739567951) 4915200000000000000000),
            (exactRationalLiteral (509799994066346443) 51200000000000000000),
            (exactRationalLiteral (8495272136099383) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1660297858773328877) 2457600000000000000000),
            (exactRationalLiteral (1517952390471041) 25600000000000000000),
            (exactRationalLiteral (-5512510190889499) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-49667618576457012589) 9830400000000000000000),
            (exactRationalLiteral (81451169911390883) 20480000000000000000),
            (exactRationalLiteral (11225292495197819) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (83852768487635993107) 4915200000000000000000),
            (exactRationalLiteral (-21232673915976089) 2048000000000000000),
            (exactRationalLiteral (958720955139263) 320000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (135398489814273244133) 2457600000000000000000),
            (exactRationalLiteral (-198932183366283707) 5120000000000000000),
            (exactRationalLiteral (2949717331128889) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-206505296566172446231) 4915200000000000000000),
            (exactRationalLiteral (2186728974252452013) 51200000000000000000),
            (exactRationalLiteral (-8614270964032307) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-47876990233153415213) 1966080000000000000000),
            (exactRationalLiteral (716346614168697003) 102400000000000000000),
            (exactRationalLiteral (10648234169015207) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-11571613016577108001) 2457600000000000000000),
            (exactRationalLiteral (-71866975220254133) 25600000000000000000),
            (exactRationalLiteral (2717526070944551) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-702072359971408833329) 4915200000000000000000),
            (exactRationalLiteral (3932780380764395019) 51200000000000000000),
            (exactRationalLiteral (-8210245704446197) 320000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1493861181029940825593) 4915200000000000000000),
            (exactRationalLiteral (-1679370837450185847) 10240000000000000000),
            (exactRationalLiteral (83006502411949169) 1600000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-702072359971408833329) 4915200000000000000000),
            (exactRationalLiteral (3932780380764395019) 51200000000000000000),
            (exactRationalLiteral (-8210245704446197) 320000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-11571613016577108001) 2457600000000000000000),
            (exactRationalLiteral (-71866975220254133) 25600000000000000000),
            (exactRationalLiteral (2717526070944551) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-47876990233153415213) 1966080000000000000000),
            (exactRationalLiteral (716346614168697003) 102400000000000000000),
            (exactRationalLiteral (10648234169015207) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-206505296566172446231) 4915200000000000000000),
            (exactRationalLiteral (2186728974252452013) 51200000000000000000),
            (exactRationalLiteral (-8614270964032307) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (135398489814273244133) 2457600000000000000000),
            (exactRationalLiteral (-198932183366283707) 5120000000000000000),
            (exactRationalLiteral (2949717331128889) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (83852768487635993107) 4915200000000000000000),
            (exactRationalLiteral (-21232673915976089) 2048000000000000000),
            (exactRationalLiteral (958720955139263) 320000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-49667618576457012589) 9830400000000000000000),
            (exactRationalLiteral (81451169911390883) 20480000000000000000),
            (exactRationalLiteral (11225292495197819) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1660297858773328877) 2457600000000000000000),
            (exactRationalLiteral (1517952390471041) 25600000000000000000),
            (exactRationalLiteral (-5512510190889499) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (44839375089739567951) 4915200000000000000000),
            (exactRationalLiteral (509799994066346443) 51200000000000000000),
            (exactRationalLiteral (8495272136099383) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4186158549378848131) 491520000000000000000),
            (exactRationalLiteral (-170545200884116931) 25600000000000000000),
            (exactRationalLiteral (-2074392719560103) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-168544910443716025223) 9830400000000000000000),
            (exactRationalLiteral (-690446934715162547) 102400000000000000000),
            (exactRationalLiteral (-12968866628017103) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4092096396174835209) 819200000000000000000),
            (exactRationalLiteral (115708308267289343) 25600000000000000000),
            (exactRationalLiteral (3061951807154259) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (17239651350764770897) 3276800000000000000000),
            (exactRationalLiteral (105647698553473999) 102400000000000000000),
            (exactRationalLiteral (-8742169418698917) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (61222054178648539) 3276800000000000000000),
            (exactRationalLiteral (362922736928558373) 102400000000000000000),
            (exactRationalLiteral (26617525580419401) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6525247871529208801) 4915200000000000000000),
            (exactRationalLiteral (-896452990144070869) 51200000000000000000),
            (exactRationalLiteral (-52058700063801433) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-11691704352913268333) 1228800000000000000000),
            (exactRationalLiteral (143732110039296547) 2560000000000000000),
            (exactRationalLiteral (49108667697442171) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (724121968538520046183) 9830400000000000000000),
            (exactRationalLiteral (-105510291202012789) 4096000000000000000),
            (exactRationalLiteral (-804569716680385361) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-35336277228737524209) 409600000000000000000),
            (exactRationalLiteral (-49427915807260991) 512000000000000000),
            (exactRationalLiteral (20820191247753681) 80000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (79586599861976287651) 9830400000000000000000),
            (exactRationalLiteral (12614893709885695103) 102400000000000000000),
            (exactRationalLiteral (-404064171699542261) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (15512903302189587289) 983040000000000000000),
            (exactRationalLiteral (-424000010587912643) 10240000000000000000),
            (exactRationalLiteral (5705686668105649) 320000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (15200517142414269) 1638400000000000000000),
            (exactRationalLiteral (-15200517142414269) 51200000000000000000),
            (exactRationalLiteral (5066839047471423) 1600000000000000000),
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
          (exactRationalLiteral (4840489878655516771) 409600000000000000000),
          (exactRationalLiteral (13674517271673077741) 153600000000000000000),
          (exactRationalLiteral (11401004209692216989) 153600000000000000000),
          (exactRationalLiteral (214102164708293263) 19200000000000000000),
          (exactRationalLiteral (234325824348440903) 122880000000000000000),
          (exactRationalLiteral (169190148017659459) 1228800000000000000000),
          (exactRationalLiteral (6501148703989342393) 1228800000000000000000),
          (exactRationalLiteral (1579090105765544429) 307200000000000000000),
          (exactRationalLiteral (284426035682622303) 16384000000000000000),
          (exactRationalLiteral (2681081550959371241) 307200000000000000000),
          (exactRationalLiteral (1159862850387099953) 122880000000000000000),
          (exactRationalLiteral (104218591053533651) 153600000000000000000),
          (exactRationalLiteral (794653673867554591) 153600000000000000000),
          (exactRationalLiteral (1335329710245072601) 76800000000000000000),
          (exactRationalLiteral (720976270317679969) 12800000000000000000),
          (exactRationalLiteral (133248969876401177) 3072000000000000000),
          (exactRationalLiteral (1257807804616051241) 51200000000000000000),
          (exactRationalLiteral (1472391004126804883) 307200000000000000000),
          (exactRationalLiteral (3718723422087062837) 25600000000000000000),
          (exactRationalLiteral (23739106992730449851) 76800000000000000000),
          (exactRationalLiteral (3718723422087062837) 25600000000000000000),
          (exactRationalLiteral (1472391004126804883) 307200000000000000000),
          (exactRationalLiteral (1257807804616051241) 51200000000000000000),
          (exactRationalLiteral (133248969876401177) 3072000000000000000),
          (exactRationalLiteral (720976270317679969) 12800000000000000000),
          (exactRationalLiteral (1335329710245072601) 76800000000000000000),
          (exactRationalLiteral (794653673867554591) 153600000000000000000),
          (exactRationalLiteral (104218591053533651) 153600000000000000000),
          (exactRationalLiteral (1159862850387099953) 122880000000000000000),
          (exactRationalLiteral (2681081550959371241) 307200000000000000000),
          (exactRationalLiteral (284426035682622303) 16384000000000000000),
          (exactRationalLiteral (1579090105765544429) 307200000000000000000),
          (exactRationalLiteral (6501148703989342393) 1228800000000000000000),
          (exactRationalLiteral (169190148017659459) 1228800000000000000000),
          (exactRationalLiteral (234325824348440903) 122880000000000000000),
          (exactRationalLiteral (214102164708293263) 19200000000000000000),
          (exactRationalLiteral (11401004209692216989) 153600000000000000000),
          (exactRationalLiteral (13674517271673077741) 153600000000000000000),
          (exactRationalLiteral (4840489878655516771) 409600000000000000000),
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
      (27, 49),
      (28, 1)
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
            (exactRationalLiteral (1688946349157141) 4915200000000000000000),
            (exactRationalLiteral (-1688946349157141) 51200000000000000000),
            (exactRationalLiteral (1688946349157141) 1600000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (65265784599949238183) 4915200000000000000000),
            (exactRationalLiteral (-1966422716301279191) 51200000000000000000),
            (exactRationalLiteral (48260234978613767) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (150048540950477201753) 9830400000000000000000),
            (exactRationalLiteral (10809311467878151367) 102400000000000000000),
            (exactRationalLiteral (-498726949304229607) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-22422786589037348389) 245760000000000000000),
            (exactRationalLiteral (-789356751601571919) 12800000000000000000),
            (exactRationalLiteral (119069615551208023) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (698298682724677199333) 9830400000000000000000),
            (exactRationalLiteral (-6026988913460013253) 102400000000000000000),
            (exactRationalLiteral (-890046100024461403) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1354601742400407083) 245760000000000000000),
            (exactRationalLiteral (923809384667766647) 12800000000000000000),
            (exactRationalLiteral (10693149907639957) 80000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-836444697829182301) 327680000000000000000),
            (exactRationalLiteral (-1113687917538518253) 51200000000000000000),
            (exactRationalLiteral (-56558763633422259) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2690486763699502531) 9830400000000000000000),
            (exactRationalLiteral (474329775563822909) 102400000000000000000),
            (exactRationalLiteral (29085993737212867) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (52244086148319579337) 9830400000000000000000),
            (exactRationalLiteral (68754989743083159) 102400000000000000000),
            (exactRationalLiteral (-9704184986496503) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2601649895765248957) 491520000000000000000),
            (exactRationalLiteral (1027517000015859) 204800000000000000),
            (exactRationalLiteral (3303706560192257) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-172846926946165746757) 9830400000000000000000),
            (exactRationalLiteral (-744176648538501467) 102400000000000000000),
            (exactRationalLiteral (-13895990283652357) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1465264246972749923) 163840000000000000000),
            (exactRationalLiteral (-178846291641150027) 25600000000000000000),
            (exactRationalLiteral (-415230531791289) 160000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (16000714445622526911) 1638400000000000000000),
            (exactRationalLiteral (544793591159114739) 51200000000000000000),
            (exactRationalLiteral (1800305282056953) 320000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1601902366810689143) 2457600000000000000000),
            (exactRationalLiteral (-21208630380482951) 25600000000000000000),
            (exactRationalLiteral (-5850781194587497) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-9414476186024644139) 1966080000000000000000),
            (exactRationalLiteral (460656539062591479) 102400000000000000000),
            (exactRationalLiteral (15475052257620713) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (80713377777361073641) 4915200000000000000000),
            (exactRationalLiteral (-517648868890047913) 51200000000000000000),
            (exactRationalLiteral (1790384728980841) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (43200567581023832821) 819200000000000000000),
            (exactRationalLiteral (-187713775049864931) 5120000000000000000),
            (exactRationalLiteral (2659486827080499) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-193872544987686901973) 4915200000000000000000),
            (exactRationalLiteral (2029060550378191173) 51200000000000000000),
            (exactRationalLiteral (-7152571423393777) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-78327558408866992337) 3276800000000000000000),
            (exactRationalLiteral (747148272907625107) 102400000000000000000),
            (exactRationalLiteral (950519040089769) 640000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-11970737906962516723) 2457600000000000000000),
            (exactRationalLiteral (-61263546894085197) 25600000000000000000),
            (exactRationalLiteral (2584188092139917) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-226319984832503469377) 1638400000000000000000),
            (exactRationalLiteral (3772744432464884531) 51200000000000000000),
            (exactRationalLiteral (-38966745627524259) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1444459458448824002939) 4915200000000000000000),
            (exactRationalLiteral (-1614633184176090239) 10240000000000000000),
            (exactRationalLiteral (78837630773289851) 1600000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-226319984832503469377) 1638400000000000000000),
            (exactRationalLiteral (3772744432464884531) 51200000000000000000),
            (exactRationalLiteral (-38966745627524259) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-11970737906962516723) 2457600000000000000000),
            (exactRationalLiteral (-61263546894085197) 25600000000000000000),
            (exactRationalLiteral (2584188092139917) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-78327558408866992337) 3276800000000000000000),
            (exactRationalLiteral (747148272907625107) 102400000000000000000),
            (exactRationalLiteral (950519040089769) 640000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-193872544987686901973) 4915200000000000000000),
            (exactRationalLiteral (2029060550378191173) 51200000000000000000),
            (exactRationalLiteral (-7152571423393777) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (43200567581023832821) 819200000000000000000),
            (exactRationalLiteral (-187713775049864931) 5120000000000000000),
            (exactRationalLiteral (2659486827080499) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (80713377777361073641) 4915200000000000000000),
            (exactRationalLiteral (-517648868890047913) 51200000000000000000),
            (exactRationalLiteral (1790384728980841) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-9414476186024644139) 1966080000000000000000),
            (exactRationalLiteral (460656539062591479) 102400000000000000000),
            (exactRationalLiteral (15475052257620713) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1601902366810689143) 2457600000000000000000),
            (exactRationalLiteral (-21208630380482951) 25600000000000000000),
            (exactRationalLiteral (-5850781194587497) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (16000714445622526911) 1638400000000000000000),
            (exactRationalLiteral (544793591159114739) 51200000000000000000),
            (exactRationalLiteral (1800305282056953) 320000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1465264246972749923) 163840000000000000000),
            (exactRationalLiteral (-178846291641150027) 25600000000000000000),
            (exactRationalLiteral (-415230531791289) 160000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-172846926946165746757) 9830400000000000000000),
            (exactRationalLiteral (-744176648538501467) 102400000000000000000),
            (exactRationalLiteral (-13895990283652357) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2601649895765248957) 491520000000000000000),
            (exactRationalLiteral (1027517000015859) 204800000000000000),
            (exactRationalLiteral (3303706560192257) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (52244086148319579337) 9830400000000000000000),
            (exactRationalLiteral (68754989743083159) 102400000000000000000),
            (exactRationalLiteral (-9704184986496503) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2690486763699502531) 9830400000000000000000),
            (exactRationalLiteral (474329775563822909) 102400000000000000000),
            (exactRationalLiteral (29085993737212867) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-836444697829182301) 327680000000000000000),
            (exactRationalLiteral (-1113687917538518253) 51200000000000000000),
            (exactRationalLiteral (-56558763633422259) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1354601742400407083) 245760000000000000000),
            (exactRationalLiteral (923809384667766647) 12800000000000000000),
            (exactRationalLiteral (10693149907639957) 80000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (698298682724677199333) 9830400000000000000000),
            (exactRationalLiteral (-6026988913460013253) 102400000000000000000),
            (exactRationalLiteral (-890046100024461403) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-22422786589037348389) 245760000000000000000),
            (exactRationalLiteral (-789356751601571919) 12800000000000000000),
            (exactRationalLiteral (119069615551208023) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (150048540950477201753) 9830400000000000000000),
            (exactRationalLiteral (10809311467878151367) 102400000000000000000),
            (exactRationalLiteral (-498726949304229607) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (65265784599949238183) 4915200000000000000000),
            (exactRationalLiteral (-1966422716301279191) 51200000000000000000),
            (exactRationalLiteral (48260234978613767) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1688946349157141) 4915200000000000000000),
            (exactRationalLiteral (-1688946349157141) 51200000000000000000),
            (exactRationalLiteral (1688946349157141) 1600000000000000000),
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
          (exactRationalLiteral (1688946349157141) 614400000000000000000),
          (exactRationalLiteral (8912495944121234287) 614400000000000000000),
          (exactRationalLiteral (1104327167464579) 60000000000000000),
          (exactRationalLiteral (4643445232083399) 50000000000000000),
          (exactRationalLiteral (29739677056527328871) 409600000000000000000),
          (exactRationalLiteral (391092423262963117) 51200000000000000000),
          (exactRationalLiteral (245050972636999) 75000000000000000),
          (exactRationalLiteral (21372316007899) 50000000000000000),
          (exactRationalLiteral (533251521350153) 100000000000000000),
          (exactRationalLiteral (109078778897211) 20000000000000000),
          (exactRationalLiteral (5344287366469117) 300000000000000000),
          (exactRationalLiteral (2749234853205721) 300000000000000000),
          (exactRationalLiteral (3031236683148979) 300000000000000000),
          (exactRationalLiteral (206018131233778063) 307200000000000000000),
          (exactRationalLiteral (1210251256760483611) 245760000000000000000),
          (exactRationalLiteral (2056829928706037941) 122880000000000000000),
          (exactRationalLiteral (16557253405935725111) 307200000000000000000),
          (exactRationalLiteral (8336277894125999103) 204800000000000000000),
          (exactRationalLiteral (29650864305029777827) 1228800000000000000000),
          (exactRationalLiteral (37069221961541) 7500000000000000),
          (exactRationalLiteral (86299516284154373483) 614400000000000000000),
          (exactRationalLiteral (183614694192450569467) 614400000000000000000),
          (exactRationalLiteral (86299516284154373483) 614400000000000000000),
          (exactRationalLiteral (37069221961541) 7500000000000000),
          (exactRationalLiteral (29650864305029777827) 1228800000000000000000),
          (exactRationalLiteral (8336277894125999103) 204800000000000000000),
          (exactRationalLiteral (16557253405935725111) 307200000000000000000),
          (exactRationalLiteral (2056829928706037941) 122880000000000000000),
          (exactRationalLiteral (1210251256760483611) 245760000000000000000),
          (exactRationalLiteral (206018131233778063) 307200000000000000000),
          (exactRationalLiteral (3031236683148979) 300000000000000000),
          (exactRationalLiteral (2749234853205721) 300000000000000000),
          (exactRationalLiteral (5344287366469117) 300000000000000000),
          (exactRationalLiteral (109078778897211) 20000000000000000),
          (exactRationalLiteral (533251521350153) 100000000000000000),
          (exactRationalLiteral (21372316007899) 50000000000000000),
          (exactRationalLiteral (245050972636999) 75000000000000000),
          (exactRationalLiteral (391092423262963117) 51200000000000000000),
          (exactRationalLiteral (29739677056527328871) 409600000000000000000),
          (exactRationalLiteral (4643445232083399) 50000000000000000),
          (exactRationalLiteral (1104327167464579) 60000000000000000),
          (exactRationalLiteral (8912495944121234287) 614400000000000000000),
          (exactRationalLiteral (1688946349157141) 614400000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 48),
      (28, 0)
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
        cell := 7
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
            (exactRationalLiteral (3632883487353533) 2400000000000000000),
            (exactRationalLiteral (-3632883487353533) 400000000000000000),
            (exactRationalLiteral (3632883487353533) 200000000000000000),
            (exactRationalLiteral (-3632883487353533) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2568127967688057) 80000000000000000),
            (exactRationalLiteral (-464298116059089) 20000000000000000),
            (exactRationalLiteral (-1329999658197153) 20000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-22190328456374541) 400000000000000000),
            (exactRationalLiteral (30224876112862747) 200000000000000000),
            (exactRationalLiteral (1416444183585333) 20000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-40254924978958897) 2400000000000000000),
            (exactRationalLiteral (-86035648380437587) 400000000000000000),
            (exactRationalLiteral (2926726511456807) 200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (129426747041636107) 2400000000000000000),
            (exactRationalLiteral (44545193959218523) 400000000000000000),
            (exactRationalLiteral (-3111136658167561) 40000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-10197493976142871) 600000000000000000),
            (exactRationalLiteral (-199789172849593) 12500000000000000),
            (exactRationalLiteral (2639960451738209) 50000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (1331470937150337) 400000000000000000),
            (exactRationalLiteral (449063869286739) 200000000000000000),
            (exactRationalLiteral (-1540896369319509) 100000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (649055272127309) 120000000000000000),
            (exactRationalLiteral (218940442325047) 200000000000000000),
            (exactRationalLiteral (44178706798937) 10000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (10810307381175853) 1200000000000000000),
            (exactRationalLiteral (862754487792097) 100000000000000000),
            (exactRationalLiteral (241436643660241) 100000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1674210593348903) 75000000000000000),
            (exactRationalLiteral (-77766831135523) 8000000000000000),
            (exactRationalLiteral (3305462003149) 25000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-34110043632426913) 2400000000000000000),
            (exactRationalLiteral (-5878172995593707) 400000000000000000),
            (exactRationalLiteral (-2499548011418161) 200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2588754847869827) 150000000000000000),
            (exactRationalLiteral (3607849866801789) 200000000000000000),
            (exactRationalLiteral (207505212916447) 25000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-2849613051421861) 2400000000000000000),
            (exactRationalLiteral (-359164371535869) 80000000000000000),
            (exactRationalLiteral (9040872826883) 8000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-74177744102707) 50000000000000000),
            (exactRationalLiteral (1312613767761951) 200000000000000000),
            (exactRationalLiteral (-80681397333) 40000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (2703843320406311) 240000000000000000),
            (exactRationalLiteral (-1798165316161761) 200000000000000000),
            (exactRationalLiteral (197730442297123) 100000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (44713337075388877) 1200000000000000000),
            (exactRationalLiteral (-4523563215580449) 200000000000000000),
            (exactRationalLiteral (1035420044061241) 100000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-56363442349526887) 2400000000000000000),
            (exactRationalLiteral (8749228868793339) 400000000000000000),
            (exactRationalLiteral (-2558984824565167) 200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-47875574851347257) 2400000000000000000),
            (exactRationalLiteral (2942129556867333) 400000000000000000),
            (exactRationalLiteral (-114831596581457) 200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3214285791029459) 600000000000000000),
            (exactRationalLiteral (32671394622781) 100000000000000000),
            (exactRationalLiteral (94708637026711) 50000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-25235911661362253) 240000000000000000),
            (exactRationalLiteral (1292952868528617) 25000000000000000),
            (exactRationalLiteral (-1723022035265029) 100000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (89052625226715463) 400000000000000000),
            (exactRationalLiteral (-22578648735379627) 200000000000000000),
            (exactRationalLiteral (3552304295440053) 100000000000000000),
            (exactRationalLiteral (-1244770389182459) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-25235911661362253) 240000000000000000),
            (exactRationalLiteral (1292952868528617) 25000000000000000),
            (exactRationalLiteral (-1723022035265029) 100000000000000000),
            (exactRationalLiteral (161814868998913) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-3214285791029459) 600000000000000000),
            (exactRationalLiteral (32671394622781) 100000000000000000),
            (exactRationalLiteral (94708637026711) 50000000000000000),
            (exactRationalLiteral (-62636306894389) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-47875574851347257) 2400000000000000000),
            (exactRationalLiteral (2942129556867333) 400000000000000000),
            (exactRationalLiteral (-114831596581457) 200000000000000000),
            (exactRationalLiteral (-227630078841811) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-56363442349526887) 2400000000000000000),
            (exactRationalLiteral (8749228868793339) 400000000000000000),
            (exactRationalLiteral (-2558984824565167) 200000000000000000),
            (exactRationalLiteral (1454591208606403) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (44713337075388877) 1200000000000000000),
            (exactRationalLiteral (-4523563215580449) 200000000000000000),
            (exactRationalLiteral (1035420044061241) 100000000000000000),
            (exactRationalLiteral (-178687396782983) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2703843320406311) 240000000000000000),
            (exactRationalLiteral (-1798165316161761) 200000000000000000),
            (exactRationalLiteral (197730442297123) 100000000000000000),
            (exactRationalLiteral (59894007731893) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-74177744102707) 50000000000000000),
            (exactRationalLiteral (1312613767761951) 200000000000000000),
            (exactRationalLiteral (-80681397333) 40000000000000),
            (exactRationalLiteral (-150340274534201) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2849613051421861) 2400000000000000000),
            (exactRationalLiteral (-359164371535869) 80000000000000000),
            (exactRationalLiteral (9040872826883) 8000000000000000),
            (exactRationalLiteral (577000331593733) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2588754847869827) 150000000000000000),
            (exactRationalLiteral (3607849866801789) 200000000000000000),
            (exactRationalLiteral (207505212916447) 25000000000000000),
            (exactRationalLiteral (83868334984899) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-34110043632426913) 2400000000000000000),
            (exactRationalLiteral (-5878172995593707) 400000000000000000),
            (exactRationalLiteral (-2499548011418161) 200000000000000000),
            (exactRationalLiteral (-1980289854254507) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1674210593348903) 75000000000000000),
            (exactRationalLiteral (-77766831135523) 8000000000000000),
            (exactRationalLiteral (3305462003149) 25000000000000000),
            (exactRationalLiteral (461957851496033) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (10810307381175853) 1200000000000000000),
            (exactRationalLiteral (862754487792097) 100000000000000000),
            (exactRationalLiteral (241436643660241) 100000000000000000),
            (exactRationalLiteral (-93318174214333) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (649055272127309) 120000000000000000),
            (exactRationalLiteral (218940442325047) 200000000000000000),
            (exactRationalLiteral (44178706798937) 10000000000000000),
            (exactRationalLiteral (760074342064223) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1331470937150337) 400000000000000000),
            (exactRationalLiteral (449063869286739) 200000000000000000),
            (exactRationalLiteral (-1540896369319509) 100000000000000000),
            (exactRationalLiteral (-829467829519103) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-10197493976142871) 600000000000000000),
            (exactRationalLiteral (-199789172849593) 12500000000000000),
            (exactRationalLiteral (2639960451738209) 50000000000000000),
            (exactRationalLiteral (223886765427899) 3750000000000000)
          ],
          ![
            (exactRationalLiteral (129426747041636107) 2400000000000000000),
            (exactRationalLiteral (44545193959218523) 400000000000000000),
            (exactRationalLiteral (-3111136658167561) 40000000000000000),
            (exactRationalLiteral (-43377828520127101) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-40254924978958897) 2400000000000000000),
            (exactRationalLiteral (-86035648380437587) 400000000000000000),
            (exactRationalLiteral (2926726511456807) 200000000000000000),
            (exactRationalLiteral (61225744742488021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-22190328456374541) 400000000000000000),
            (exactRationalLiteral (30224876112862747) 200000000000000000),
            (exactRationalLiteral (1416444183585333) 20000000000000000),
            (exactRationalLiteral (-8185421794643431) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (2568127967688057) 80000000000000000),
            (exactRationalLiteral (-464298116059089) 20000000000000000),
            (exactRationalLiteral (-1329999658197153) 20000000000000000),
            (exactRationalLiteral (208286495496893) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (3632883487353533) 2400000000000000000),
            (exactRationalLiteral (-3632883487353533) 400000000000000000),
            (exactRationalLiteral (3632883487353533) 200000000000000000),
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
          (exactRationalLiteral (752865296771777) 15000000000000000),
          (exactRationalLiteral (250848335515319) 2343750000000000),
          (exactRationalLiteral (2378707769202221) 25000000000000000),
          (exactRationalLiteral (14556590800738721) 150000000000000000),
          (exactRationalLiteral (1576125259936317) 50000000000000000),
          (exactRationalLiteral (353032355775607) 50000000000000000),
          (exactRationalLiteral (2308202398570141) 300000000000000000),
          (exactRationalLiteral (4131126972620123) 300000000000000000),
          (exactRationalLiteral (2676521536101071) 100000000000000000),
          (exactRationalLiteral (637744755288719) 25000000000000000),
          (exactRationalLiteral (8568813985829011) 300000000000000000),
          (exactRationalLiteral (27510240518977) 10000000000000000),
          (exactRationalLiteral (1392879067269329) 300000000000000000),
          (exactRationalLiteral (1207951365888283) 75000000000000000),
          (exactRationalLiteral (3870396815291431) 75000000000000000),
          (exactRationalLiteral (11467834329776101) 300000000000000000),
          (exactRationalLiteral (7102353529106477) 300000000000000000),
          (exactRationalLiteral (170215106478667) 30000000000000000),
          (exactRationalLiteral (40756688183322203) 300000000000000000),
          (exactRationalLiteral (21674719072611743) 75000000000000000),
          (exactRationalLiteral (40756688183322203) 300000000000000000),
          (exactRationalLiteral (170215106478667) 30000000000000000),
          (exactRationalLiteral (7102353529106477) 300000000000000000),
          (exactRationalLiteral (11467834329776101) 300000000000000000),
          (exactRationalLiteral (3870396815291431) 75000000000000000),
          (exactRationalLiteral (1207951365888283) 75000000000000000),
          (exactRationalLiteral (1392879067269329) 300000000000000000),
          (exactRationalLiteral (27510240518977) 10000000000000000),
          (exactRationalLiteral (8568813985829011) 300000000000000000),
          (exactRationalLiteral (637744755288719) 25000000000000000),
          (exactRationalLiteral (2676521536101071) 100000000000000000),
          (exactRationalLiteral (4131126972620123) 300000000000000000),
          (exactRationalLiteral (2308202398570141) 300000000000000000),
          (exactRationalLiteral (353032355775607) 50000000000000000),
          (exactRationalLiteral (1576125259936317) 50000000000000000),
          (exactRationalLiteral (14556590800738721) 150000000000000000),
          (exactRationalLiteral (2378707769202221) 25000000000000000),
          (exactRationalLiteral (250848335515319) 2343750000000000),
          (exactRationalLiteral (752865296771777) 15000000000000000),
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
      (46, 13),
      (46, 14)
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
theorem generatorCoordinates28_valid : ∀ i, (generatorCoordinates28 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
