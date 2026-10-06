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

/-- Actual coordinate interval candidates, block 27. -/
def generatorCoordinates27 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 6
        lower := (exactRationalLiteral (1) 16)
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
            (exactRationalLiteral (41191712509593511849) 4915200000000000000000),
            (exactRationalLiteral (-1420403879641155581) 51200000000000000000),
            (exactRationalLiteral (48979444125557089) 1600000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (127377110659329580739) 4915200000000000000000),
            (exactRationalLiteral (3065870367025874481) 51200000000000000000),
            (exactRationalLiteral (-227984987954583541) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-297306920041929079681) 3276800000000000000000),
            (exactRationalLiteral (1630211807877569727) 102400000000000000000),
            (exactRationalLiteral (826551937161393237) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (69947765352449322179) 1228800000000000000000),
            (exactRationalLiteral (-1589540771992890951) 12800000000000000000),
            (exactRationalLiteral (-90491614822946629) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (16455369260787909907) 3276800000000000000000),
            (exactRationalLiteral (10308850417032016851) 102400000000000000000),
            (exactRationalLiteral (61324653358520637) 640000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2148294798134703569) 409600000000000000000),
            (exactRationalLiteral (-2898372063155493) 102400000000000000),
            (exactRationalLiteral (-7533396232406811) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-526079943970633651) 983040000000000000000),
            (exactRationalLiteral (289577926641764459) 51200000000000000000),
            (exactRationalLiteral (1288425268253861) 320000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (4163136397297958543) 9830400000000000000000),
            (exactRationalLiteral (-186846356257058971) 102400000000000000000),
            (exactRationalLiteral (-5472560457895657) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (34203506793807122861) 9830400000000000000000),
            (exactRationalLiteral (47015849282046723) 20480000000000000000),
            (exactRationalLiteral (3764032962669701) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7336138638886847701) 2457600000000000000000),
            (exactRationalLiteral (38199920822111199) 25600000000000000000),
            (exactRationalLiteral (-16171996467943) 160000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-44281116123943139763) 3276800000000000000000),
            (exactRationalLiteral (-329433665662989043) 102400000000000000000),
            (exactRationalLiteral (-916259104758801) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-472786766631438217) 98304000000000000000),
            (exactRationalLiteral (-63271638982955171) 25600000000000000000),
            (exactRationalLiteral (-2051513507407657) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (3570884976606591421) 983040000000000000000),
            (exactRationalLiteral (239159787663837643) 51200000000000000000),
            (exactRationalLiteral (1913966571689417) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6664747514309309869) 2457600000000000000000),
            (exactRationalLiteral (34766576613360333) 5120000000000000000),
            (exactRationalLiteral (-44599485712621) 32000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-96015570453810672499) 9830400000000000000000),
            (exactRationalLiteral (1259959439505605999) 102400000000000000000),
            (exactRationalLiteral (-44021584416299803) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (161370210879437078989) 4915200000000000000000),
            (exactRationalLiteral (-1795172672025440817) 51200000000000000000),
            (exactRationalLiteral (43835465382997477) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (255644903412657080923) 2457600000000000000000),
            (exactRationalLiteral (-90083078990668351) 1024000000000000000),
            (exactRationalLiteral (6722713883757959) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-7048612559317444059) 65536000000000000000),
            (exactRationalLiteral (6896711648579967533) 51200000000000000000),
            (exactRationalLiteral (-27616364992333197) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-221854492920401413247) 9830400000000000000000),
            (exactRationalLiteral (-1830087533995524117) 102400000000000000000),
            (exactRationalLiteral (87291540760377913) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (716928080213387393) 2457600000000000000000),
            (exactRationalLiteral (-258246567745337077) 25600000000000000000),
            (exactRationalLiteral (4450919795404793) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1110399556792798790479) 4915200000000000000000),
            (exactRationalLiteral (6771999482331279627) 51200000000000000000),
            (exactRationalLiteral (-68149506153418423) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2353789038487484307239) 4915200000000000000000),
            (exactRationalLiteral (-14122270926539135507) 51200000000000000000),
            (exactRationalLiteral (137201833714520303) 1600000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1110399556792798790479) 4915200000000000000000),
            (exactRationalLiteral (6771999482331279627) 51200000000000000000),
            (exactRationalLiteral (-68149506153418423) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (716928080213387393) 2457600000000000000000),
            (exactRationalLiteral (-258246567745337077) 25600000000000000000),
            (exactRationalLiteral (4450919795404793) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-221854492920401413247) 9830400000000000000000),
            (exactRationalLiteral (-1830087533995524117) 102400000000000000000),
            (exactRationalLiteral (87291540760377913) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-7048612559317444059) 65536000000000000000),
            (exactRationalLiteral (6896711648579967533) 51200000000000000000),
            (exactRationalLiteral (-27616364992333197) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (255644903412657080923) 2457600000000000000000),
            (exactRationalLiteral (-90083078990668351) 1024000000000000000),
            (exactRationalLiteral (6722713883757959) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (161370210879437078989) 4915200000000000000000),
            (exactRationalLiteral (-1795172672025440817) 51200000000000000000),
            (exactRationalLiteral (43835465382997477) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-96015570453810672499) 9830400000000000000000),
            (exactRationalLiteral (1259959439505605999) 102400000000000000000),
            (exactRationalLiteral (-44021584416299803) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-6664747514309309869) 2457600000000000000000),
            (exactRationalLiteral (34766576613360333) 5120000000000000000),
            (exactRationalLiteral (-44599485712621) 32000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (3570884976606591421) 983040000000000000000),
            (exactRationalLiteral (239159787663837643) 51200000000000000000),
            (exactRationalLiteral (1913966571689417) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-472786766631438217) 98304000000000000000),
            (exactRationalLiteral (-63271638982955171) 25600000000000000000),
            (exactRationalLiteral (-2051513507407657) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-44281116123943139763) 3276800000000000000000),
            (exactRationalLiteral (-329433665662989043) 102400000000000000000),
            (exactRationalLiteral (-916259104758801) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7336138638886847701) 2457600000000000000000),
            (exactRationalLiteral (38199920822111199) 25600000000000000000),
            (exactRationalLiteral (-16171996467943) 160000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (34203506793807122861) 9830400000000000000000),
            (exactRationalLiteral (47015849282046723) 20480000000000000000),
            (exactRationalLiteral (3764032962669701) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4163136397297958543) 9830400000000000000000),
            (exactRationalLiteral (-186846356257058971) 102400000000000000000),
            (exactRationalLiteral (-5472560457895657) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-526079943970633651) 983040000000000000000),
            (exactRationalLiteral (289577926641764459) 51200000000000000000),
            (exactRationalLiteral (1288425268253861) 320000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2148294798134703569) 409600000000000000000),
            (exactRationalLiteral (-2898372063155493) 102400000000000000),
            (exactRationalLiteral (-7533396232406811) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (16455369260787909907) 3276800000000000000000),
            (exactRationalLiteral (10308850417032016851) 102400000000000000000),
            (exactRationalLiteral (61324653358520637) 640000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (69947765352449322179) 1228800000000000000000),
            (exactRationalLiteral (-1589540771992890951) 12800000000000000000),
            (exactRationalLiteral (-90491614822946629) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-297306920041929079681) 3276800000000000000000),
            (exactRationalLiteral (1630211807877569727) 102400000000000000000),
            (exactRationalLiteral (826551937161393237) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (127377110659329580739) 4915200000000000000000),
            (exactRationalLiteral (3065870367025874481) 51200000000000000000),
            (exactRationalLiteral (-227984987954583541) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (41191712509593511849) 4915200000000000000000),
            (exactRationalLiteral (-1420403879641155581) 51200000000000000000),
            (exactRationalLiteral (48979444125557089) 1600000000000000000),
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
          (exactRationalLiteral (15200517142414269) 1638400000000000000),
          (exactRationalLiteral (424689477179257801) 15360000000000000000),
          (exactRationalLiteral (11180310690745356821) 122880000000000000000),
          (exactRationalLiteral (3101559520595955639) 51200000000000000000),
          (exactRationalLiteral (1268277978783836747) 153600000000000000000),
          (exactRationalLiteral (118003055716629097) 19200000000000000000),
          (exactRationalLiteral (434694636121230413) 614400000000000000000),
          (exactRationalLiteral (196084314609043823) 409600000000000000000),
          (exactRationalLiteral (545618056627217719) 153600000000000000000),
          (exactRationalLiteral (116415885918479393) 38400000000000000000),
          (exactRationalLiteral (2091169714186882507) 153600000000000000000),
          (exactRationalLiteral (12516291149194523) 2560000000000000000),
          (exactRationalLiteral (96759892046232453) 25600000000000000000),
          (exactRationalLiteral (179735549735907811) 61440000000000000000),
          (exactRationalLiteral (12491204800682200169) 1228800000000000000000),
          (exactRationalLiteral (20861092112710718951) 614400000000000000000),
          (exactRationalLiteral (32812837577684212201) 307200000000000000000),
          (exactRationalLiteral (68719247077285600163) 614400000000000000000),
          (exactRationalLiteral (236547738249574099) 10240000000000000000),
          (exactRationalLiteral (37627180295625383) 61440000000000000000),
          (exactRationalLiteral (141365130749962529749) 614400000000000000000),
          (exactRationalLiteral (299571192650508075541) 614400000000000000000),
          (exactRationalLiteral (141365130749962529749) 614400000000000000000),
          (exactRationalLiteral (37627180295625383) 61440000000000000000),
          (exactRationalLiteral (236547738249574099) 10240000000000000000),
          (exactRationalLiteral (68719247077285600163) 614400000000000000000),
          (exactRationalLiteral (32812837577684212201) 307200000000000000000),
          (exactRationalLiteral (20861092112710718951) 614400000000000000000),
          (exactRationalLiteral (12491204800682200169) 1228800000000000000000),
          (exactRationalLiteral (179735549735907811) 61440000000000000000),
          (exactRationalLiteral (96759892046232453) 25600000000000000000),
          (exactRationalLiteral (12516291149194523) 2560000000000000000),
          (exactRationalLiteral (2091169714186882507) 153600000000000000000),
          (exactRationalLiteral (116415885918479393) 38400000000000000000),
          (exactRationalLiteral (545618056627217719) 153600000000000000000),
          (exactRationalLiteral (196084314609043823) 409600000000000000000),
          (exactRationalLiteral (434694636121230413) 614400000000000000000),
          (exactRationalLiteral (118003055716629097) 19200000000000000000),
          (exactRationalLiteral (1268277978783836747) 153600000000000000000),
          (exactRationalLiteral (3101559520595955639) 51200000000000000000),
          (exactRationalLiteral (11180310690745356821) 122880000000000000000),
          (exactRationalLiteral (424689477179257801) 15360000000000000000),
          (exactRationalLiteral (15200517142414269) 1638400000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
      (31, 17),
      (31, 1),
      (30, 49),
      (30, 33),
      (30, 17),
      (30, 1),
      (29, 49),
      (29, 33),
      (29, 17),
      (29, 1),
      (28, 49),
      (28, 33),
      (28, 17),
      (28, 1),
      (27, 49),
      (27, 33),
      (27, 17),
      (27, 1),
      (26, 49),
      (26, 33),
      (26, 17),
      (26, 1),
      (25, 49),
      (25, 33),
      (25, 17),
      (25, 1),
      (24, 49),
      (24, 33),
      (24, 17),
      (24, 1),
      (23, 49),
      (23, 33),
      (23, 17),
      (23, 30),
      (23, 46),
      (23, 62),
      (24, 14),
      (24, 30),
      (24, 46),
      (24, 62),
      (25, 14),
      (25, 30),
      (25, 46),
      (25, 62),
      (26, 14),
      (26, 30),
      (26, 46),
      (26, 62),
      (27, 14),
      (27, 30),
      (27, 46),
      (27, 62),
      (28, 14)
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
            (exactRationalLiteral (11081176996820002101) 1638400000000000000000),
            (exactRationalLiteral (-1231241888535555789) 51200000000000000000),
            (exactRationalLiteral (45601551427242807) 1600000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (143115440212582167221) 4915200000000000000000),
            (exactRationalLiteral (2193394018483711361) 51200000000000000000),
            (exactRationalLiteral (-208253186316498019) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-872599517143003851221) 9830400000000000000000),
            (exactRationalLiteral (4747094001313767983) 102400000000000000000),
            (exactRationalLiteral (731889159556705891) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (19794831993288791799) 409600000000000000000),
            (exactRationalLiteral (-1921569912659798231) 12800000000000000000),
            (exactRationalLiteral (-75522955510507011) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (114556783952690764879) 9830400000000000000000),
            (exactRationalLiteral (11364390717514277507) 102400000000000000000),
            (exactRationalLiteral (221146883448527143) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-8691635869196581733) 1228800000000000000000),
            (exactRationalLiteral (-383715929142548641) 12800000000000000000),
            (exactRationalLiteral (-3176314391649197) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-166725379637166629) 983040000000000000000),
            (exactRationalLiteral (306346304867600027) 51200000000000000000),
            (exactRationalLiteral (1942062771648479) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (995420468962676899) 3276800000000000000000),
            (exactRationalLiteral (-203799661775054667) 102400000000000000000),
            (exactRationalLiteral (-3004092301102191) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (11885100868516456873) 3276800000000000000000),
            (exactRationalLiteral (248211347125317247) 102400000000000000000),
            (exactRationalLiteral (560403478974423) 640000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2521778287681196769) 819200000000000000000),
            (exactRationalLiteral (7671998079765667) 5120000000000000000),
            (exactRationalLiteral (160894770698283) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-5393386158787480007) 393216000000000000000),
            (exactRationalLiteral (-66990589878658951) 20480000000000000000),
            (exactRationalLiteral (-368676552078811) 640000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12223924201530163703) 2457600000000000000000),
            (exactRationalLiteral (-71481212891378483) 25600000000000000000),
            (exactRationalLiteral (-2053273446803999) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (3862875244994599499) 983040000000000000000),
            (exactRationalLiteral (9913126499958643) 2048000000000000000),
            (exactRationalLiteral (2420220845874799) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5636483145637078171) 2457600000000000000000),
            (exactRationalLiteral (168696392488143569) 25600000000000000000),
            (exactRationalLiteral (-1453258146513523) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-17793414758144588513) 1966080000000000000000),
            (exactRationalLiteral (43694904854610103) 4096000000000000000),
            (exactRationalLiteral (-39771824653876909) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (30222637510338708383) 983040000000000000000),
            (exactRationalLiteral (-1625837250586881857) 51200000000000000000),
            (exactRationalLiteral (40832245336282003) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (242529999787001338013) 2457600000000000000000),
            (exactRationalLiteral (-424105000426406699) 5120000000000000000),
            (exactRationalLiteral (6432483379709569) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-488893419966055720447) 4915200000000000000000),
            (exactRationalLiteral (6359001344139688893) 51200000000000000000),
            (exactRationalLiteral (-26154665451694667) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-231811102191124288441) 9830400000000000000000),
            (exactRationalLiteral (-1492712648891145189) 102400000000000000000),
            (exactRationalLiteral (81395901791811551) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-779673640628996089) 2457600000000000000000),
            (exactRationalLiteral (-240709564521327173) 25600000000000000000),
            (exactRationalLiteral (4317581816600159) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1070577016041073306889) 4915200000000000000000),
            (exactRationalLiteral (6503570423507019387) 51200000000000000000),
            (exactRationalLiteral (-66065023258711697) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2270685159446269100561) 4915200000000000000000),
            (exactRationalLiteral (-13581801334958372931) 51200000000000000000),
            (exactRationalLiteral (26606592415172197) 320000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-1070577016041073306889) 4915200000000000000000),
            (exactRationalLiteral (6503570423507019387) 51200000000000000000),
            (exactRationalLiteral (-66065023258711697) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-779673640628996089) 2457600000000000000000),
            (exactRationalLiteral (-240709564521327173) 25600000000000000000),
            (exactRationalLiteral (4317581816600159) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-231811102191124288441) 9830400000000000000000),
            (exactRationalLiteral (-1492712648891145189) 102400000000000000000),
            (exactRationalLiteral (81395901791811551) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-488893419966055720447) 4915200000000000000000),
            (exactRationalLiteral (6359001344139688893) 51200000000000000000),
            (exactRationalLiteral (-26154665451694667) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (242529999787001338013) 2457600000000000000000),
            (exactRationalLiteral (-424105000426406699) 5120000000000000000),
            (exactRationalLiteral (6432483379709569) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (30222637510338708383) 983040000000000000000),
            (exactRationalLiteral (-1625837250586881857) 51200000000000000000),
            (exactRationalLiteral (40832245336282003) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-17793414758144588513) 1966080000000000000000),
            (exactRationalLiteral (43694904854610103) 4096000000000000000),
            (exactRationalLiteral (-39771824653876909) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-5636483145637078171) 2457600000000000000000),
            (exactRationalLiteral (168696392488143569) 25600000000000000000),
            (exactRationalLiteral (-1453258146513523) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (3862875244994599499) 983040000000000000000),
            (exactRationalLiteral (9913126499958643) 2048000000000000000),
            (exactRationalLiteral (2420220845874799) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-12223924201530163703) 2457600000000000000000),
            (exactRationalLiteral (-71481212891378483) 25600000000000000000),
            (exactRationalLiteral (-2053273446803999) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-5393386158787480007) 393216000000000000000),
            (exactRationalLiteral (-66990589878658951) 20480000000000000000),
            (exactRationalLiteral (-368676552078811) 640000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2521778287681196769) 819200000000000000000),
            (exactRationalLiteral (7671998079765667) 5120000000000000000),
            (exactRationalLiteral (160894770698283) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (11885100868516456873) 3276800000000000000000),
            (exactRationalLiteral (248211347125317247) 102400000000000000000),
            (exactRationalLiteral (560403478974423) 640000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (995420468962676899) 3276800000000000000000),
            (exactRationalLiteral (-203799661775054667) 102400000000000000000),
            (exactRationalLiteral (-3004092301102191) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-166725379637166629) 983040000000000000000),
            (exactRationalLiteral (306346304867600027) 51200000000000000000),
            (exactRationalLiteral (1942062771648479) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8691635869196581733) 1228800000000000000000),
            (exactRationalLiteral (-383715929142548641) 12800000000000000000),
            (exactRationalLiteral (-3176314391649197) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (114556783952690764879) 9830400000000000000000),
            (exactRationalLiteral (11364390717514277507) 102400000000000000000),
            (exactRationalLiteral (221146883448527143) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (19794831993288791799) 409600000000000000000),
            (exactRationalLiteral (-1921569912659798231) 12800000000000000000),
            (exactRationalLiteral (-75522955510507011) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-872599517143003851221) 9830400000000000000000),
            (exactRationalLiteral (4747094001313767983) 102400000000000000000),
            (exactRationalLiteral (731889159556705891) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (143115440212582167221) 4915200000000000000000),
            (exactRationalLiteral (2193394018483711361) 51200000000000000000),
            (exactRationalLiteral (-208253186316498019) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (11081176996820002101) 1638400000000000000000),
            (exactRationalLiteral (-1231241888535555789) 51200000000000000000),
            (exactRationalLiteral (45601551427242807) 1600000000000000000),
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
          (exactRationalLiteral (18635091076237856251) 614400000000000000000),
          (exactRationalLiteral (13821840629366760841) 153600000000000000000),
          (exactRationalLiteral (1014299258150906707) 19200000000000000000),
          (exactRationalLiteral (6219610773496130867) 409600000000000000000),
          (exactRationalLiteral (82084450490656637) 10240000000000000000),
          (exactRationalLiteral (9086404128587903) 25600000000000000000),
          (exactRationalLiteral (56053341894242053) 153600000000000000000),
          (exactRationalLiteral (4550982711415754989) 1228800000000000000000),
          (exactRationalLiteral (192025459898217229) 61440000000000000000),
          (exactRationalLiteral (5660229438665661843) 409600000000000000000),
          (exactRationalLiteral (311113213512860233) 61440000000000000000),
          (exactRationalLiteral (2508171812768076601) 614400000000000000000),
          (exactRationalLiteral (96043171281862507) 38400000000000000000),
          (exactRationalLiteral (1443213000135336601) 153600000000000000000),
          (exactRationalLiteral (2439292150773224863) 76800000000000000000),
          (exactRationalLiteral (1296816602189339599) 12800000000000000000),
          (exactRationalLiteral (7943224972329715679) 76800000000000000000),
          (exactRationalLiteral (29506000031488321567) 1228800000000000000000),
          (exactRationalLiteral (186114532216572431) 307200000000000000000),
          (exactRationalLiteral (5678577940743842987) 25600000000000000000),
          (exactRationalLiteral (36122371043331111437) 76800000000000000000),
          (exactRationalLiteral (5678577940743842987) 25600000000000000000),
          (exactRationalLiteral (186114532216572431) 307200000000000000000),
          (exactRationalLiteral (29506000031488321567) 1228800000000000000000),
          (exactRationalLiteral (7943224972329715679) 76800000000000000000),
          (exactRationalLiteral (1296816602189339599) 12800000000000000000),
          (exactRationalLiteral (2439292150773224863) 76800000000000000000),
          (exactRationalLiteral (1443213000135336601) 153600000000000000000),
          (exactRationalLiteral (96043171281862507) 38400000000000000000),
          (exactRationalLiteral (2508171812768076601) 614400000000000000000),
          (exactRationalLiteral (311113213512860233) 61440000000000000000),
          (exactRationalLiteral (5660229438665661843) 409600000000000000000),
          (exactRationalLiteral (192025459898217229) 61440000000000000000),
          (exactRationalLiteral (4550982711415754989) 1228800000000000000000),
          (exactRationalLiteral (56053341894242053) 153600000000000000000),
          (exactRationalLiteral (9086404128587903) 25600000000000000000),
          (exactRationalLiteral (82084450490656637) 10240000000000000000),
          (exactRationalLiteral (6219610773496130867) 409600000000000000000),
          (exactRationalLiteral (1014299258150906707) 19200000000000000000),
          (exactRationalLiteral (13821840629366760841) 153600000000000000000),
          (exactRationalLiteral (18635091076237856251) 614400000000000000000),
          (exactRationalLiteral (579308597760899363) 76800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 61),
      (28, 13)
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
            (exactRationalLiteral (1688946349157141) 314572800000000000),
            (exactRationalLiteral (-1688946349157141) 81920000000000000),
            (exactRationalLiteral (1688946349157141) 64000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (153855693294238801247) 4915200000000000000000),
            (exactRationalLiteral (1399844876493890329) 51200000000000000000),
            (exactRationalLiteral (-188521384678412497) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-167142586866171904403) 1966080000000000000000),
            (exactRationalLiteral (1497065016866243371) 20480000000000000000),
            (exactRationalLiteral (127445276390403709) 640000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (47008675675031260351) 1228800000000000000000),
            (exactRationalLiteral (-2193724416076947039) 12800000000000000000),
            (exactRationalLiteral (-60554296198067393) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (185054985325782451469) 9830400000000000000000),
            (exactRationalLiteral (2415605096924046799) 20480000000000000000),
            (exactRationalLiteral (135670500104451101) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-11014618889388633487) 1228800000000000000000),
            (exactRationalLiteral (-387707023027630201) 12800000000000000000),
            (exactRationalLiteral (1180767449108417) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (336585143333688487) 1638400000000000000000),
            (exactRationalLiteral (305114428814952291) 51200000000000000000),
            (exactRationalLiteral (-2558000797972347) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1737288201251650267) 9830400000000000000000),
            (exactRationalLiteral (-210879094665876499) 102400000000000000000),
            (exactRationalLiteral (-21424965772349) 128000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (37174346834768549137) 9830400000000000000000),
            (exactRationalLiteral (51499077113842107) 20480000000000000000),
            (exactRationalLiteral (1840001827074529) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1559678512339418341) 491520000000000000000),
            (exactRationalLiteral (39487078987697463) 25600000000000000000),
            (exactRationalLiteral (402649523736281) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-136870200753794038381) 9830400000000000000000),
            (exactRationalLiteral (-344180727746141483) 102400000000000000000),
            (exactRationalLiteral (-2770506416029309) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4225819266665889319) 819200000000000000000),
            (exactRationalLiteral (-79697826557387163) 25600000000000000000),
            (exactRationalLiteral (-2055033386200341) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (6944137622404677687) 1638400000000000000000),
            (exactRationalLiteral (51704310886167207) 10240000000000000000),
            (exactRationalLiteral (2926475120060181) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-185723878899246841) 98304000000000000000),
            (exactRationalLiteral (162206817894693481) 25600000000000000000),
            (exactRationalLiteral (-1791529150211521) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-82873100919328258447) 9830400000000000000000),
            (exactRationalLiteral (941784842274590727) 102400000000000000000),
            (exactRationalLiteral (-7104412978290803) 640000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (141836138112020772913) 4915200000000000000000),
            (exactRationalLiteral (-1468514709335184793) 51200000000000000000),
            (exactRationalLiteral (37829025289566529) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (76728998055636914461) 819200000000000000000),
            (exactRationalLiteral (-398955527915665203) 5120000000000000000),
            (exactRationalLiteral (6142252875661179) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-452279457837506496509) 4915200000000000000000),
            (exactRationalLiteral (5850525030512180853) 51200000000000000000),
            (exactRationalLiteral (-24692965911056137) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-79938069939614562137) 3276800000000000000000),
            (exactRationalLiteral (-1178920319661031709) 102400000000000000000),
            (exactRationalLiteral (75500262823245189) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-434530679574595151) 491520000000000000000),
            (exactRationalLiteral (-44741182642507161) 5120000000000000000),
            (exactRationalLiteral (167369753511821) 32000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-344113345282518968009) 1638400000000000000000),
            (exactRationalLiteral (6243479296261586051) 51200000000000000000),
            (exactRationalLiteral (-63980540364004971) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2190774071494874557523) 4915200000000000000000),
            (exactRationalLiteral (-13058007229932247627) 51200000000000000000),
            (exactRationalLiteral (128864090437201667) 1600000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-344113345282518968009) 1638400000000000000000),
            (exactRationalLiteral (6243479296261586051) 51200000000000000000),
            (exactRationalLiteral (-63980540364004971) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-434530679574595151) 491520000000000000000),
            (exactRationalLiteral (-44741182642507161) 5120000000000000000),
            (exactRationalLiteral (167369753511821) 32000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-79938069939614562137) 3276800000000000000000),
            (exactRationalLiteral (-1178920319661031709) 102400000000000000000),
            (exactRationalLiteral (75500262823245189) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-452279457837506496509) 4915200000000000000000),
            (exactRationalLiteral (5850525030512180853) 51200000000000000000),
            (exactRationalLiteral (-24692965911056137) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (76728998055636914461) 819200000000000000000),
            (exactRationalLiteral (-398955527915665203) 5120000000000000000),
            (exactRationalLiteral (6142252875661179) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (141836138112020772913) 4915200000000000000000),
            (exactRationalLiteral (-1468514709335184793) 51200000000000000000),
            (exactRationalLiteral (37829025289566529) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-82873100919328258447) 9830400000000000000000),
            (exactRationalLiteral (941784842274590727) 102400000000000000000),
            (exactRationalLiteral (-7104412978290803) 640000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-185723878899246841) 98304000000000000000),
            (exactRationalLiteral (162206817894693481) 25600000000000000000),
            (exactRationalLiteral (-1791529150211521) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (6944137622404677687) 1638400000000000000000),
            (exactRationalLiteral (51704310886167207) 10240000000000000000),
            (exactRationalLiteral (2926475120060181) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4225819266665889319) 819200000000000000000),
            (exactRationalLiteral (-79697826557387163) 25600000000000000000),
            (exactRationalLiteral (-2055033386200341) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-136870200753794038381) 9830400000000000000000),
            (exactRationalLiteral (-344180727746141483) 102400000000000000000),
            (exactRationalLiteral (-2770506416029309) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1559678512339418341) 491520000000000000000),
            (exactRationalLiteral (39487078987697463) 25600000000000000000),
            (exactRationalLiteral (402649523736281) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (37174346834768549137) 9830400000000000000000),
            (exactRationalLiteral (51499077113842107) 20480000000000000000),
            (exactRationalLiteral (1840001827074529) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1737288201251650267) 9830400000000000000000),
            (exactRationalLiteral (-210879094665876499) 102400000000000000000),
            (exactRationalLiteral (-21424965772349) 128000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (336585143333688487) 1638400000000000000000),
            (exactRationalLiteral (305114428814952291) 51200000000000000000),
            (exactRationalLiteral (-2558000797972347) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-11014618889388633487) 1228800000000000000000),
            (exactRationalLiteral (-387707023027630201) 12800000000000000000),
            (exactRationalLiteral (1180767449108417) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (185054985325782451469) 9830400000000000000000),
            (exactRationalLiteral (2415605096924046799) 20480000000000000000),
            (exactRationalLiteral (135670500104451101) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (47008675675031260351) 1228800000000000000000),
            (exactRationalLiteral (-2193724416076947039) 12800000000000000000),
            (exactRationalLiteral (-60554296198067393) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-167142586866171904403) 1966080000000000000000),
            (exactRationalLiteral (1497065016866243371) 20480000000000000000),
            (exactRationalLiteral (127445276390403709) 640000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (153855693294238801247) 4915200000000000000000),
            (exactRationalLiteral (1399844876493890329) 51200000000000000000),
            (exactRationalLiteral (-188521384678412497) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (1688946349157141) 314572800000000000),
            (exactRationalLiteral (-1688946349157141) 81920000000000000),
            (exactRationalLiteral (1688946349157141) 64000000000000000),
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
          (exactRationalLiteral (3710615129098238777) 614400000000000000000),
          (exactRationalLiteral (307616268887703667) 9600000000000000000),
          (exactRationalLiteral (35675412460383115553) 409600000000000000000),
          (exactRationalLiteral (1335017542625291987) 30720000000000000000),
          (exactRationalLiteral (432916670094305603) 19200000000000000000),
          (exactRationalLiteral (23773474834382461) 2400000000000000000),
          (exactRationalLiteral (748115110260623) 1920000000000000000),
          (exactRationalLiteral (295885547342244607) 1228800000000000000000),
          (exactRationalLiteral (24708249992951501) 6400000000000000000),
          (exactRationalLiteral (161095837902993) 50000000000000000),
          (exactRationalLiteral (269358433629117907) 19200000000000000000),
          (exactRationalLiteral (1261984107402161) 240000000000000000),
          (exactRationalLiteral (1688828912734673) 384000000000000000),
          (exactRationalLiteral (641865359764254629) 307200000000000000000),
          (exactRationalLiteral (2145178663017690103) 245760000000000000000),
          (exactRationalLiteral (18294583865739798077) 614400000000000000000),
          (exactRationalLiteral (29533023306880095011) 307200000000000000000),
          (exactRationalLiteral (19591878402773353227) 204800000000000000000),
          (exactRationalLiteral (474858237907893221) 19200000000000000000),
          (exactRationalLiteral (5529853662083201) 4800000000000000000),
          (exactRationalLiteral (131407932199860128807) 614400000000000000000),
          (exactRationalLiteral (278792096236475279383) 614400000000000000000),
          (exactRationalLiteral (131407932199860128807) 614400000000000000000),
          (exactRationalLiteral (5529853662083201) 4800000000000000000),
          (exactRationalLiteral (474858237907893221) 19200000000000000000),
          (exactRationalLiteral (19591878402773353227) 204800000000000000000),
          (exactRationalLiteral (29533023306880095011) 307200000000000000000),
          (exactRationalLiteral (18294583865739798077) 614400000000000000000),
          (exactRationalLiteral (2145178663017690103) 245760000000000000000),
          (exactRationalLiteral (641865359764254629) 307200000000000000000),
          (exactRationalLiteral (1688828912734673) 384000000000000000),
          (exactRationalLiteral (1261984107402161) 240000000000000000),
          (exactRationalLiteral (269358433629117907) 19200000000000000000),
          (exactRationalLiteral (161095837902993) 50000000000000000),
          (exactRationalLiteral (24708249992951501) 6400000000000000000),
          (exactRationalLiteral (295885547342244607) 1228800000000000000000),
          (exactRationalLiteral (748115110260623) 1920000000000000000),
          (exactRationalLiteral (23773474834382461) 2400000000000000000),
          (exactRationalLiteral (432916670094305603) 19200000000000000000),
          (exactRationalLiteral (1335017542625291987) 30720000000000000000),
          (exactRationalLiteral (35675412460383115553) 409600000000000000000),
          (exactRationalLiteral (307616268887703667) 9600000000000000000),
          (exactRationalLiteral (3710615129098238777) 614400000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 60),
      (28, 12)
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
            (exactRationalLiteral (20549410230194934547) 4915200000000000000000),
            (exactRationalLiteral (-893452618704127589) 51200000000000000000),
            (exactRationalLiteral (38845766030614243) 1600000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (32014286628722707069) 983040000000000000000),
            (exactRationalLiteral (137044588211282277) 10240000000000000000),
            (exactRationalLiteral (-6751583321613079) 64000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-261177639450622249243) 3276800000000000000000),
            (exactRationalLiteral (9844905056929916343) 102400000000000000000),
            (exactRationalLiteral (542563604347331199) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (33179552261442527873) 1228800000000000000000),
            (exactRationalLiteral (-19248034257954699) 102400000000000000),
            (exactRationalLiteral (-1823425475425111) 16000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (86269759567126988161) 3276800000000000000000),
            (exactRationalLiteral (2489950943669977263) 20480000000000000000),
            (exactRationalLiteral (50194116760375059) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4436421163600694411) 409600000000000000000),
            (exactRationalLiteral (-74853957909936261) 2560000000000000000),
            (exactRationalLiteral (5537849289866031) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2791745739036627739) 4915200000000000000000),
            (exactRationalLiteral (285882298483821251) 51200000000000000000),
            (exactRationalLiteral (-7058064367593173) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (475460016151860437) 9830400000000000000000),
            (exactRationalLiteral (-208084654929524467) 102400000000000000000),
            (exactRationalLiteral (1932844012484741) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (38737551107837516351) 9830400000000000000000),
            (exactRationalLiteral (262931361741913479) 102400000000000000000),
            (exactRationalLiteral (877986259276943) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8041113848920263847) 2457600000000000000000),
            (exactRationalLiteral (41581186588718583) 25600000000000000000),
            (exactRationalLiteral (644404276774279) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-46324079897295260001) 3276800000000000000000),
            (exactRationalLiteral (-357117000721529227) 102400000000000000000),
            (exactRationalLiteral (-3697630071664563) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2636062439946796079) 491520000000000000000),
            (exactRationalLiteral (-87921479980981211) 25600000000000000000),
            (exactRationalLiteral (-2056793325596683) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (22420684912336512971) 4915200000000000000000),
            (exactRationalLiteral (271239963459447523) 51200000000000000000),
            (exactRationalLiteral (3432729394245563) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3692707498930340383) 2457600000000000000000),
            (exactRationalLiteral (154364159286451401) 25600000000000000000),
            (exactRationalLiteral (-2129800153909519) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-77631657605328470689) 9830400000000000000000),
            (exactRationalLiteral (161639220446724091) 20480000000000000000),
            (exactRationalLiteral (-31272305129031121) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (133466985279297600607) 4915200000000000000000),
            (exactRationalLiteral (-10585640386162797) 409600000000000000),
            (exactRationalLiteral (6965161048570211) 320000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (218581058891899490233) 2457600000000000000000),
            (exactRationalLiteral (-374966977421117267) 5120000000000000000),
            (exactRationalLiteral (5852022371612789) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-139542883872761336337) 1638400000000000000000),
            (exactRationalLiteral (5371282707697443413) 51200000000000000000),
            (exactRationalLiteral (-23231266370417607) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-49201062227761039969) 1966080000000000000000),
            (exactRationalLiteral (-888710546305183677) 102400000000000000000),
            (exactRationalLiteral (69604623854678827) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3465211303009862821) 2457600000000000000000),
            (exactRationalLiteral (-207235613818962973) 25600000000000000000),
            (exactRationalLiteral (4050905858990891) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-995638588622776620469) 4915200000000000000000),
            (exactRationalLiteral (5991726100594979619) 51200000000000000000),
            (exactRationalLiteral (-12379211493859649) 320000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2113955721713972854493) 4915200000000000000000),
            (exactRationalLiteral (-2510177722292151919) 10240000000000000000),
            (exactRationalLiteral (124695218798542349) 1600000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-995638588622776620469) 4915200000000000000000),
            (exactRationalLiteral (5991726100594979619) 51200000000000000000),
            (exactRationalLiteral (-12379211493859649) 320000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3465211303009862821) 2457600000000000000000),
            (exactRationalLiteral (-207235613818962973) 25600000000000000000),
            (exactRationalLiteral (4050905858990891) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-49201062227761039969) 1966080000000000000000),
            (exactRationalLiteral (-888710546305183677) 102400000000000000000),
            (exactRationalLiteral (69604623854678827) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-139542883872761336337) 1638400000000000000000),
            (exactRationalLiteral (5371282707697443413) 51200000000000000000),
            (exactRationalLiteral (-23231266370417607) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (218581058891899490233) 2457600000000000000000),
            (exactRationalLiteral (-374966977421117267) 5120000000000000000),
            (exactRationalLiteral (5852022371612789) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (133466985279297600607) 4915200000000000000000),
            (exactRationalLiteral (-10585640386162797) 409600000000000000),
            (exactRationalLiteral (6965161048570211) 320000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-77631657605328470689) 9830400000000000000000),
            (exactRationalLiteral (161639220446724091) 20480000000000000000),
            (exactRationalLiteral (-31272305129031121) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3692707498930340383) 2457600000000000000000),
            (exactRationalLiteral (154364159286451401) 25600000000000000000),
            (exactRationalLiteral (-2129800153909519) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (22420684912336512971) 4915200000000000000000),
            (exactRationalLiteral (271239963459447523) 51200000000000000000),
            (exactRationalLiteral (3432729394245563) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2636062439946796079) 491520000000000000000),
            (exactRationalLiteral (-87921479980981211) 25600000000000000000),
            (exactRationalLiteral (-2056793325596683) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-46324079897295260001) 3276800000000000000000),
            (exactRationalLiteral (-357117000721529227) 102400000000000000000),
            (exactRationalLiteral (-3697630071664563) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8041113848920263847) 2457600000000000000000),
            (exactRationalLiteral (41581186588718583) 25600000000000000000),
            (exactRationalLiteral (644404276774279) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (38737551107837516351) 9830400000000000000000),
            (exactRationalLiteral (262931361741913479) 102400000000000000000),
            (exactRationalLiteral (877986259276943) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (475460016151860437) 9830400000000000000000),
            (exactRationalLiteral (-208084654929524467) 102400000000000000000),
            (exactRationalLiteral (1932844012484741) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2791745739036627739) 4915200000000000000000),
            (exactRationalLiteral (285882298483821251) 51200000000000000000),
            (exactRationalLiteral (-7058064367593173) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4436421163600694411) 409600000000000000000),
            (exactRationalLiteral (-74853957909936261) 2560000000000000000),
            (exactRationalLiteral (5537849289866031) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (86269759567126988161) 3276800000000000000000),
            (exactRationalLiteral (2489950943669977263) 20480000000000000000),
            (exactRationalLiteral (50194116760375059) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (33179552261442527873) 1228800000000000000000),
            (exactRationalLiteral (-19248034257954699) 102400000000000000),
            (exactRationalLiteral (-1823425475425111) 16000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-261177639450622249243) 3276800000000000000000),
            (exactRationalLiteral (9844905056929916343) 102400000000000000000),
            (exactRationalLiteral (542563604347331199) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (32014286628722707069) 983040000000000000000),
            (exactRationalLiteral (137044588211282277) 10240000000000000000),
            (exactRationalLiteral (-6751583321613079) 64000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (20549410230194934547) 4915200000000000000000),
            (exactRationalLiteral (-893452618704127589) 51200000000000000000),
            (exactRationalLiteral (38845766030614243) 1600000000000000000),
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
          (exactRationalLiteral (20203824889810103917) 614400000000000000000),
          (exactRationalLiteral (1584751193985961249) 19200000000000000000),
          (exactRationalLiteral (13103295529903137) 400000000000000000),
          (exactRationalLiteral (37033298376879963823) 1228800000000000000000),
          (exactRationalLiteral (1801660096332643781) 153600000000000000000),
          (exactRationalLiteral (30216403413337513) 40960000000000000000),
          (exactRationalLiteral (718931171158523) 6400000000000000000),
          (exactRationalLiteral (4941062268007148603) 1228800000000000000000),
          (exactRationalLiteral (1020988937361657679) 307200000000000000000),
          (exactRationalLiteral (140055147146093179) 9830400000000000000),
          (exactRationalLiteral (560426995817642177) 102400000000000000000),
          (exactRationalLiteral (193707967650289041) 40960000000000000000),
          (exactRationalLiteral (8128945784667137) 4800000000000000000),
          (exactRationalLiteral (156547241615815697) 19200000000000000000),
          (exactRationalLiteral (268637850488008907) 9600000000000000000),
          (exactRationalLiteral (438074354423926879) 4800000000000000000),
          (exactRationalLiteral (169958837103821953) 1920000000000000000),
          (exactRationalLiteral (10352732363568374899) 409600000000000000000),
          (exactRationalLiteral (509354011984897673) 307200000000000000000),
          (exactRationalLiteral (1980079096364095327) 9600000000000000000),
          (exactRationalLiteral (4203094839141738457) 9600000000000000000),
          (exactRationalLiteral (1980079096364095327) 9600000000000000000),
          (exactRationalLiteral (509354011984897673) 307200000000000000000),
          (exactRationalLiteral (10352732363568374899) 409600000000000000000),
          (exactRationalLiteral (169958837103821953) 1920000000000000000),
          (exactRationalLiteral (438074354423926879) 4800000000000000000),
          (exactRationalLiteral (268637850488008907) 9600000000000000000),
          (exactRationalLiteral (156547241615815697) 19200000000000000000),
          (exactRationalLiteral (8128945784667137) 4800000000000000000),
          (exactRationalLiteral (193707967650289041) 40960000000000000000),
          (exactRationalLiteral (560426995817642177) 102400000000000000000),
          (exactRationalLiteral (140055147146093179) 9830400000000000000),
          (exactRationalLiteral (1020988937361657679) 307200000000000000000),
          (exactRationalLiteral (4941062268007148603) 1228800000000000000000),
          (exactRationalLiteral (718931171158523) 6400000000000000000),
          (exactRationalLiteral (30216403413337513) 40960000000000000000),
          (exactRationalLiteral (1801660096332643781) 153600000000000000000),
          (exactRationalLiteral (37033298376879963823) 1228800000000000000000),
          (exactRationalLiteral (13103295529903137) 400000000000000000),
          (exactRationalLiteral (1584751193985961249) 19200000000000000000),
          (exactRationalLiteral (20203824889810103917) 614400000000000000000),
          (exactRationalLiteral (15200517142414269) 3200000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 59),
      (28, 11)
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
            (exactRationalLiteral (5213777379848094267) 1638400000000000000000),
            (exactRationalLiteral (-744825339978299181) 51200000000000000000),
            (exactRationalLiteral (35467873332299961) 1600000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (162236223000020422043) 4915200000000000000000),
            (exactRationalLiteral (49528212171274529) 51200000000000000000),
            (exactRationalLiteral (-149057781402241453) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-718331375868538024667) 9830400000000000000000),
            (exactRationalLiteral (11825833919109866447) 102400000000000000000),
            (exactRationalLiteral (447900826742643853) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1217091570839915253) 81920000000000000000),
            (exactRationalLiteral (-2558409511161969239) 12800000000000000000),
            (exactRationalLiteral (-30616977573188157) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (333768230879228478913) 9830400000000000000000),
            (exactRationalLiteral (12479578418703234467) 102400000000000000000),
            (exactRationalLiteral (-35282266583700983) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3094199941851749647) 245760000000000000000),
            (exactRationalLiteral (-343404228708701953) 12800000000000000000),
            (exactRationalLiteral (1978986226124729) 80000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (880868500649990773) 983040000000000000000),
            (exactRationalLiteral (248649913874206907) 51200000000000000000),
            (exactRationalLiteral (-11558127937213999) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-246659970882765203) 3276800000000000000000),
            (exactRationalLiteral (-195416342565998571) 102400000000000000000),
            (exactRationalLiteral (4401312169278207) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (13440609017043043399) 3276800000000000000000),
            (exactRationalLiteral (264519275643426079) 102400000000000000000),
            (exactRationalLiteral (-84029308520643) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (553286722585734579) 163840000000000000000),
            (exactRationalLiteral (8928462640378339) 5120000000000000000),
            (exactRationalLiteral (886159029812277) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-141163021751697471137) 9830400000000000000000),
            (exactRationalLiteral (-373761768319457987) 102400000000000000000),
            (exactRationalLiteral (-4624753727299817) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-549301185571384529) 98304000000000000000),
            (exactRationalLiteral (-96152173162160627) 25600000000000000000),
            (exactRationalLiteral (-82342130599721) 32000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (24091342462920886393) 4915200000000000000000),
            (exactRationalLiteral (285983389584800539) 51200000000000000000),
            (exactRationalLiteral (787796733686189) 320000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2793433229073338197) 2457600000000000000000),
            (exactRationalLiteral (145168416663417329) 25600000000000000000),
            (exactRationalLiteral (-2468071157607517) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-14628149922885085967) 1966080000000000000000),
            (exactRationalLiteral (691606401242341759) 102400000000000000000),
            (exactRationalLiteral (-27022545366608227) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (125933651772402853621) 4915200000000000000000),
            (exactRationalLiteral (-1189908267392376353) 51200000000000000000),
            (exactRationalLiteral (31822585196135581) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (207677366301481771763) 2457600000000000000000),
            (exactRationalLiteral (-352139348942762891) 5120000000000000000),
            (exactRationalLiteral (5561791867564399) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-387765597363511634353) 4915200000000000000000),
            (exactRationalLiteral (4921274375695476573) 51200000000000000000),
            (exactRationalLiteral (-21769566829779077) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-250525901486254421431) 9830400000000000000000),
            (exactRationalLiteral (-622083328823601093) 102400000000000000000),
            (exactRationalLiteral (12741796977222493) 640000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4660547467530968503) 2457600000000000000000),
            (exactRationalLiteral (-191298666340608677) 25600000000000000000),
            (exactRationalLiteral (3917567880186257) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-960422646777259494791) 4915200000000000000000),
            (exactRationalLiteral (5748310836507200091) 51200000000000000000),
            (exactRationalLiteral (-59811574574591519) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2040130057184236167839) 4915200000000000000000),
            (exactRationalLiteral (-2412089095908781767) 10240000000000000000),
            (exactRationalLiteral (120526347159883031) 1600000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-960422646777259494791) 4915200000000000000000),
            (exactRationalLiteral (5748310836507200091) 51200000000000000000),
            (exactRationalLiteral (-59811574574591519) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4660547467530968503) 2457600000000000000000),
            (exactRationalLiteral (-191298666340608677) 25600000000000000000),
            (exactRationalLiteral (3917567880186257) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-250525901486254421431) 9830400000000000000000),
            (exactRationalLiteral (-622083328823601093) 102400000000000000000),
            (exactRationalLiteral (12741796977222493) 640000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-387765597363511634353) 4915200000000000000000),
            (exactRationalLiteral (4921274375695476573) 51200000000000000000),
            (exactRationalLiteral (-21769566829779077) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (207677366301481771763) 2457600000000000000000),
            (exactRationalLiteral (-352139348942762891) 5120000000000000000),
            (exactRationalLiteral (5561791867564399) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (125933651772402853621) 4915200000000000000000),
            (exactRationalLiteral (-1189908267392376353) 51200000000000000000),
            (exactRationalLiteral (31822585196135581) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-14628149922885085967) 1966080000000000000000),
            (exactRationalLiteral (691606401242341759) 102400000000000000000),
            (exactRationalLiteral (-27022545366608227) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-2793433229073338197) 2457600000000000000000),
            (exactRationalLiteral (145168416663417329) 25600000000000000000),
            (exactRationalLiteral (-2468071157607517) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (24091342462920886393) 4915200000000000000000),
            (exactRationalLiteral (285983389584800539) 51200000000000000000),
            (exactRationalLiteral (787796733686189) 320000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-549301185571384529) 98304000000000000000),
            (exactRationalLiteral (-96152173162160627) 25600000000000000000),
            (exactRationalLiteral (-82342130599721) 32000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-141163021751697471137) 9830400000000000000000),
            (exactRationalLiteral (-373761768319457987) 102400000000000000000),
            (exactRationalLiteral (-4624753727299817) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (553286722585734579) 163840000000000000000),
            (exactRationalLiteral (8928462640378339) 5120000000000000000),
            (exactRationalLiteral (886159029812277) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (13440609017043043399) 3276800000000000000000),
            (exactRationalLiteral (264519275643426079) 102400000000000000000),
            (exactRationalLiteral (-84029308520643) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-246659970882765203) 3276800000000000000000),
            (exactRationalLiteral (-195416342565998571) 102400000000000000000),
            (exactRationalLiteral (4401312169278207) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (880868500649990773) 983040000000000000000),
            (exactRationalLiteral (248649913874206907) 51200000000000000000),
            (exactRationalLiteral (-11558127937213999) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3094199941851749647) 245760000000000000000),
            (exactRationalLiteral (-343404228708701953) 12800000000000000000),
            (exactRationalLiteral (1978986226124729) 80000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (333768230879228478913) 9830400000000000000000),
            (exactRationalLiteral (12479578418703234467) 102400000000000000000),
            (exactRationalLiteral (-35282266583700983) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1217091570839915253) 81920000000000000000),
            (exactRationalLiteral (-2558409511161969239) 12800000000000000000),
            (exactRationalLiteral (-30616977573188157) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-718331375868538024667) 9830400000000000000000),
            (exactRationalLiteral (11825833919109866447) 102400000000000000000),
            (exactRationalLiteral (447900826742643853) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (162236223000020422043) 4915200000000000000000),
            (exactRationalLiteral (49528212171274529) 51200000000000000000),
            (exactRationalLiteral (-149057781402241453) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (5213777379848094267) 1638400000000000000000),
            (exactRationalLiteral (-744825339978299181) 51200000000000000000),
            (exactRationalLiteral (35467873332299961) 1600000000000000000),
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
          (exactRationalLiteral (2247987590728154671) 614400000000000000000),
          (exactRationalLiteral (5075779471649215477) 153600000000000000000),
          (exactRationalLiteral (94052230469604668597) 1228800000000000000000),
          (exactRationalLiteral (3229033354213606529) 153600000000000000000),
          (exactRationalLiteral (1932595735124557507) 51200000000000000000),
          (exactRationalLiteral (85777859693086481) 6400000000000000000),
          (exactRationalLiteral (79896372332439409) 76800000000000000000),
          (exactRationalLiteral (20496730777500937) 153600000000000000000),
          (exactRationalLiteral (642416434099217933) 153600000000000000000),
          (exactRationalLiteral (5272504458036031) 1536000000000000000),
          (exactRationalLiteral (741138775414924803) 51200000000000000000),
          (exactRationalLiteral (219174417164621443) 38400000000000000000),
          (exactRationalLiteral (390021292340901149) 76800000000000000000),
          (exactRationalLiteral (404521694629320467) 307200000000000000000),
          (exactRationalLiteral (1882469033353337281) 245760000000000000000),
          (exactRationalLiteral (3240008648504793679) 122880000000000000000),
          (exactRationalLiteral (8876817041245700087) 102400000000000000000),
          (exactRationalLiteral (50357452280237043319) 614400000000000000000),
          (exactRationalLiteral (3940687067774237039) 153600000000000000000),
          (exactRationalLiteral (16321116974692619) 7680000000000000000),
          (exactRationalLiteral (40743669010498009291) 204800000000000000000),
          (exactRationalLiteral (259584382137520859137) 614400000000000000000),
          (exactRationalLiteral (40743669010498009291) 204800000000000000000),
          (exactRationalLiteral (16321116974692619) 7680000000000000000),
          (exactRationalLiteral (3940687067774237039) 153600000000000000000),
          (exactRationalLiteral (50357452280237043319) 614400000000000000000),
          (exactRationalLiteral (8876817041245700087) 102400000000000000000),
          (exactRationalLiteral (3240008648504793679) 122880000000000000000),
          (exactRationalLiteral (1882469033353337281) 245760000000000000000),
          (exactRationalLiteral (404521694629320467) 307200000000000000000),
          (exactRationalLiteral (390021292340901149) 76800000000000000000),
          (exactRationalLiteral (219174417164621443) 38400000000000000000),
          (exactRationalLiteral (741138775414924803) 51200000000000000000),
          (exactRationalLiteral (5272504458036031) 1536000000000000000),
          (exactRationalLiteral (642416434099217933) 153600000000000000000),
          (exactRationalLiteral (20496730777500937) 153600000000000000000),
          (exactRationalLiteral (79896372332439409) 76800000000000000000),
          (exactRationalLiteral (85777859693086481) 6400000000000000000),
          (exactRationalLiteral (1932595735124557507) 51200000000000000000),
          (exactRationalLiteral (3229033354213606529) 153600000000000000000),
          (exactRationalLiteral (94052230469604668597) 1228800000000000000000),
          (exactRationalLiteral (5075779471649215477) 153600000000000000000),
          (exactRationalLiteral (2247987590728154671) 614400000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 58),
      (28, 10)
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
            (exactRationalLiteral (11584483008868830119) 4915200000000000000000),
            (exactRationalLiteral (-609709632045727901) 51200000000000000000),
            (exactRationalLiteral (32089980633985679) 1600000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (160823626102773513869) 4915200000000000000000),
            (exactRationalLiteral (-507239310161520239) 51200000000000000000),
            (exactRationalLiteral (-129325979764155931) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-642380213543385849133) 9830400000000000000000),
            (exactRationalLiteral (13428111670871067167) 102400000000000000000),
            (exactRationalLiteral (353238049137956507) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2598387401998413949) 1228800000000000000000),
            (exactRationalLiteral (-2650940102829842631) 12800000000000000000),
            (exactRationalLiteral (-15648318260748539) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (407880408659067169751) 9830400000000000000000),
            (exactRationalLiteral (12167496585680278451) 102400000000000000000),
            (exactRationalLiteral (-4830345997111081) 128000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-17395257580580445757) 1228800000000000000000),
            (exactRationalLiteral (-59022068100938429) 2560000000000000000),
            (exactRationalLiteral (14252012971381259) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (382636279798009601) 327680000000000000000),
            (exactRationalLiteral (193417274986109259) 51200000000000000000),
            (exactRationalLiteral (-642327660273393) 64000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1849788349385774687) 9830400000000000000000),
            (exactRationalLiteral (-172874157575298811) 102400000000000000000),
            (exactRationalLiteral (6869780326071673) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (41904086291016248611) 9830400000000000000000),
            (exactRationalLiteral (52451825454749667) 20480000000000000000),
            (exactRationalLiteral (-1046044876318229) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8578755645367268171) 2457600000000000000000),
            (exactRationalLiteral (48670458827216799) 25600000000000000000),
            (exactRationalLiteral (45116551314011) 32000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-143464797900964357879) 9830400000000000000000),
            (exactRationalLiteral (-394115030539927763) 102400000000000000000),
            (exactRationalLiteral (-5551877382935071) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-955610157146338577) 163840000000000000000),
            (exactRationalLiteral (-104389906100925411) 25600000000000000000),
            (exactRationalLiteral (-2060313204389367) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (1723769041436506833) 327680000000000000000),
            (exactRationalLiteral (302751832806895083) 51200000000000000000),
            (exactRationalLiteral (4445237942616327) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1953392666998916419) 2457600000000000000000),
            (exactRationalLiteral (26923918005118253) 5120000000000000000),
            (exactRationalLiteral (-561268432261103) 160000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-69298382712320986429) 9830400000000000000000),
            (exactRationalLiteral (592015739300754639) 102400000000000000000),
            (exactRationalLiteral (-22772785604185333) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (119164060310215360579) 4915200000000000000000),
            (exactRationalLiteral (-1068624366701264977) 51200000000000000000),
            (exactRationalLiteral (28819365149420107) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (65813696245057260391) 819200000000000000000),
            (exactRationalLiteral (-13218905699224083) 204800000000000000),
            (exactRationalLiteral (5271561363516009) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-71902978225662549787) 983040000000000000000),
            (exactRationalLiteral (4500500034506280333) 51200000000000000000),
            (exactRationalLiteral (-20307867289140547) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-84505825398812314619) 3276800000000000000000),
            (exactRationalLiteral (-379038667216283957) 102400000000000000000),
            (exactRationalLiteral (57813345917546103) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5761862002927604017) 2457600000000000000000),
            (exactRationalLiteral (-175895070777472917) 25600000000000000000),
            (exactRationalLiteral (3784229901381623) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-308880727573844188523) 1638400000000000000000),
            (exactRationalLiteral (5513233503998247467) 51200000000000000000),
            (exactRationalLiteral (-57727091679884793) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1969197024986336673929) 4915200000000000000000),
            (exactRationalLiteral (-11586677834181695347) 51200000000000000000),
            (exactRationalLiteral (116357475521223713) 1600000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-308880727573844188523) 1638400000000000000000),
            (exactRationalLiteral (5513233503998247467) 51200000000000000000),
            (exactRationalLiteral (-57727091679884793) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5761862002927604017) 2457600000000000000000),
            (exactRationalLiteral (-175895070777472917) 25600000000000000000),
            (exactRationalLiteral (3784229901381623) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-84505825398812314619) 3276800000000000000000),
            (exactRationalLiteral (-379038667216283957) 102400000000000000000),
            (exactRationalLiteral (57813345917546103) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-71902978225662549787) 983040000000000000000),
            (exactRationalLiteral (4500500034506280333) 51200000000000000000),
            (exactRationalLiteral (-20307867289140547) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (65813696245057260391) 819200000000000000000),
            (exactRationalLiteral (-13218905699224083) 204800000000000000),
            (exactRationalLiteral (5271561363516009) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (119164060310215360579) 4915200000000000000000),
            (exactRationalLiteral (-1068624366701264977) 51200000000000000000),
            (exactRationalLiteral (28819365149420107) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-69298382712320986429) 9830400000000000000000),
            (exactRationalLiteral (592015739300754639) 102400000000000000000),
            (exactRationalLiteral (-22772785604185333) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1953392666998916419) 2457600000000000000000),
            (exactRationalLiteral (26923918005118253) 5120000000000000000),
            (exactRationalLiteral (-561268432261103) 160000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (1723769041436506833) 327680000000000000000),
            (exactRationalLiteral (302751832806895083) 51200000000000000000),
            (exactRationalLiteral (4445237942616327) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-955610157146338577) 163840000000000000000),
            (exactRationalLiteral (-104389906100925411) 25600000000000000000),
            (exactRationalLiteral (-2060313204389367) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-143464797900964357879) 9830400000000000000000),
            (exactRationalLiteral (-394115030539927763) 102400000000000000000),
            (exactRationalLiteral (-5551877382935071) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8578755645367268171) 2457600000000000000000),
            (exactRationalLiteral (48670458827216799) 25600000000000000000),
            (exactRationalLiteral (45116551314011) 32000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (41904086291016248611) 9830400000000000000000),
            (exactRationalLiteral (52451825454749667) 20480000000000000000),
            (exactRationalLiteral (-1046044876318229) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1849788349385774687) 9830400000000000000000),
            (exactRationalLiteral (-172874157575298811) 102400000000000000000),
            (exactRationalLiteral (6869780326071673) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (382636279798009601) 327680000000000000000),
            (exactRationalLiteral (193417274986109259) 51200000000000000000),
            (exactRationalLiteral (-642327660273393) 64000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-17395257580580445757) 1228800000000000000000),
            (exactRationalLiteral (-59022068100938429) 2560000000000000000),
            (exactRationalLiteral (14252012971381259) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (407880408659067169751) 9830400000000000000000),
            (exactRationalLiteral (12167496585680278451) 102400000000000000000),
            (exactRationalLiteral (-4830345997111081) 128000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2598387401998413949) 1228800000000000000000),
            (exactRationalLiteral (-2650940102829842631) 12800000000000000000),
            (exactRationalLiteral (-15648318260748539) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-642380213543385849133) 9830400000000000000000),
            (exactRationalLiteral (13428111670871067167) 102400000000000000000),
            (exactRationalLiteral (353238049137956507) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (160823626102773513869) 4915200000000000000000),
            (exactRationalLiteral (-507239310161520239) 51200000000000000000),
            (exactRationalLiteral (-129325979764155931) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (11584483008868830119) 4915200000000000000000),
            (exactRationalLiteral (-609709632045727901) 51200000000000000000),
            (exactRationalLiteral (32089980633985679) 1600000000000000000),
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
          (exactRationalLiteral (164012162907023069) 19200000000000000000),
          (exactRationalLiteral (55497235534331579501) 1228800000000000000000),
          (exactRationalLiteral (2279456752782499951) 153600000000000000000),
          (exactRationalLiteral (783671426952894613) 614400000000000000000),
          (exactRationalLiteral (97773635293960807) 409600000000000000000),
          (exactRationalLiteral (1778635188767693339) 409600000000000000000),
          (exactRationalLiteral (363677985023916183) 102400000000000000000),
          (exactRationalLiteral (18083032773320095501) 1228800000000000000000),
          (exactRationalLiteral (366337597377018029) 61440000000000000000),
          (exactRationalLiteral (3347297495116653677) 614400000000000000000),
          (exactRationalLiteral (7392191650180493) 7680000000000000000),
          (exactRationalLiteral (1111638643233078403) 153600000000000000000),
          (exactRationalLiteral (1913404579934230837) 76800000000000000000),
          (exactRationalLiteral (3163718396392088647) 38400000000000000000),
          (exactRationalLiteral (1944399289010522367) 25600000000000000000),
          (exactRationalLiteral (1272420499899087203) 49152000000000000000),
          (exactRationalLiteral (784782649318160027) 307200000000000000000),
          (exactRationalLiteral (14739939167968973683) 76800000000000000000),
          (exactRationalLiteral (31317315864863511887) 76800000000000000000),
          (exactRationalLiteral (14739939167968973683) 76800000000000000000),
          (exactRationalLiteral (784782649318160027) 307200000000000000000),
          (exactRationalLiteral (1272420499899087203) 49152000000000000000),
          (exactRationalLiteral (1944399289010522367) 25600000000000000000),
          (exactRationalLiteral (3163718396392088647) 38400000000000000000),
          (exactRationalLiteral (1913404579934230837) 76800000000000000000),
          (exactRationalLiteral (1111638643233078403) 153600000000000000000),
          (exactRationalLiteral (7392191650180493) 7680000000000000000),
          (exactRationalLiteral (3347297495116653677) 614400000000000000000),
          (exactRationalLiteral (366337597377018029) 61440000000000000000),
          (exactRationalLiteral (18083032773320095501) 1228800000000000000000),
          (exactRationalLiteral (363677985023916183) 102400000000000000000),
          (exactRationalLiteral (1778635188767693339) 409600000000000000000),
          (exactRationalLiteral (97773635293960807) 409600000000000000000),
          (exactRationalLiteral (783671426952894613) 614400000000000000000),
          (exactRationalLiteral (2279456752782499951) 153600000000000000000),
          (exactRationalLiteral (55497235534331579501) 1228800000000000000000),
          (exactRationalLiteral (164012162907023069) 19200000000000000000),
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
      (27, 57),
      (28, 9)
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
            (exactRationalLiteral (8297793413409033733) 4915200000000000000000),
            (exactRationalLiteral (-488105494906413749) 51200000000000000000),
            (exactRationalLiteral (28712087935671397) 1600000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (156307205691186863351) 4915200000000000000000),
            (exactRationalLiteral (-985079625941972919) 51200000000000000000),
            (exactRationalLiteral (-109594178126070409) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-185983779346307572477) 3276800000000000000000),
            (exactRationalLiteral (14651738312213518503) 102400000000000000000),
            (exactRationalLiteral (258575271533269161) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-13435158396859865833) 1228800000000000000000),
            (exactRationalLiteral (-2683596057247957551) 12800000000000000000),
            (exactRationalLiteral (-679658948308921) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (159698126280213070663) 3276800000000000000000),
            (exactRationalLiteral (11513509219281018267) 102400000000000000000),
            (exactRationalLiteral (-206235033271853067) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6325822380196331021) 409600000000000000000),
            (exactRationalLiteral (-229388124937651881) 12800000000000000000),
            (exactRationalLiteral (18609094812138873) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1337869858905259673) 983040000000000000000),
            (exactRationalLiteral (120184381819528307) 51200000000000000000),
            (exactRationalLiteral (-20558255076455651) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2794722058297533613) 9830400000000000000000),
            (exactRationalLiteral (-140458099957425187) 102400000000000000000),
            (exactRationalLiteral (9338248482865139) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (43461240453871729529) 9830400000000000000000),
            (exactRationalLiteral (256150916632880247) 102400000000000000000),
            (exactRationalLiteral (-401612088823163) 640000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8885280382736924257) 2457600000000000000000),
            (exactRationalLiteral (10733124692938779) 5120000000000000000),
            (exactRationalLiteral (1369668535888273) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1945330921432289151) 131072000000000000000),
            (exactRationalLiteral (-83635357476587711) 20480000000000000000),
            (exactRationalLiteral (-259160041542813) 128000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-14985222592010888893) 2457600000000000000000),
            (exactRationalLiteral (-112634678797275563) 25600000000000000000),
            (exactRationalLiteral (-2062073143785709) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (5545682898159422089) 983040000000000000000),
            (exactRationalLiteral (64309058625146231) 10240000000000000000),
            (exactRationalLiteral (4951492216801709) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1180704316795827001) 2457600000000000000000),
            (exactRationalLiteral (122717679372973209) 25600000000000000000),
            (exactRationalLiteral (-3144613165003513) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-13200512532943398203) 1966080000000000000000),
            (exactRationalLiteral (101884823281771819) 20480000000000000000),
            (exactRationalLiteral (-18523025841762439) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (22617226722322790021) 983040000000000000000),
            (exactRationalLiteral (-959353346197015497) 51200000000000000000),
            (exactRationalLiteral (25816145102704633) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (187837398532483711663) 2457600000000000000000),
            (exactRationalLiteral (-309966858034634819) 5120000000000000000),
            (exactRationalLiteral (4981330859467619) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-111233709655936909719) 1638400000000000000000),
            (exactRationalLiteral (4108959684129854693) 51200000000000000000),
            (exactRationalLiteral (-18846167748502017) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-255121530604598359811) 9830400000000000000000),
            (exactRationalLiteral (-159576561483232269) 102400000000000000000),
            (exactRationalLiteral (51917706948979741) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-6772355020691080579) 2457600000000000000000),
            (exactRationalLiteral (-161024827129555693) 25600000000000000000),
            (exactRationalLiteral (3650891922576989) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-894247168866122871379) 4915200000000000000000),
            (exactRationalLiteral (5286494103068121747) 51200000000000000000),
            (exactRationalLiteral (-55642608785178067) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1901056572200946549131) 4915200000000000000000),
            (exactRationalLiteral (-11129585675374119131) 51200000000000000000),
            (exactRationalLiteral (22437720776512879) 320000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-894247168866122871379) 4915200000000000000000),
            (exactRationalLiteral (5286494103068121747) 51200000000000000000),
            (exactRationalLiteral (-55642608785178067) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6772355020691080579) 2457600000000000000000),
            (exactRationalLiteral (-161024827129555693) 25600000000000000000),
            (exactRationalLiteral (3650891922576989) 800000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-255121530604598359811) 9830400000000000000000),
            (exactRationalLiteral (-159576561483232269) 102400000000000000000),
            (exactRationalLiteral (51917706948979741) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-111233709655936909719) 1638400000000000000000),
            (exactRationalLiteral (4108959684129854693) 51200000000000000000),
            (exactRationalLiteral (-18846167748502017) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (187837398532483711663) 2457600000000000000000),
            (exactRationalLiteral (-309966858034634819) 5120000000000000000),
            (exactRationalLiteral (4981330859467619) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (22617226722322790021) 983040000000000000000),
            (exactRationalLiteral (-959353346197015497) 51200000000000000000),
            (exactRationalLiteral (25816145102704633) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-13200512532943398203) 1966080000000000000000),
            (exactRationalLiteral (101884823281771819) 20480000000000000000),
            (exactRationalLiteral (-18523025841762439) 3200000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1180704316795827001) 2457600000000000000000),
            (exactRationalLiteral (122717679372973209) 25600000000000000000),
            (exactRationalLiteral (-3144613165003513) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (5545682898159422089) 983040000000000000000),
            (exactRationalLiteral (64309058625146231) 10240000000000000000),
            (exactRationalLiteral (4951492216801709) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-14985222592010888893) 2457600000000000000000),
            (exactRationalLiteral (-112634678797275563) 25600000000000000000),
            (exactRationalLiteral (-2062073143785709) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1945330921432289151) 131072000000000000000),
            (exactRationalLiteral (-83635357476587711) 20480000000000000000),
            (exactRationalLiteral (-259160041542813) 128000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8885280382736924257) 2457600000000000000000),
            (exactRationalLiteral (10733124692938779) 5120000000000000000),
            (exactRationalLiteral (1369668535888273) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (43461240453871729529) 9830400000000000000000),
            (exactRationalLiteral (256150916632880247) 102400000000000000000),
            (exactRationalLiteral (-401612088823163) 640000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-2794722058297533613) 9830400000000000000000),
            (exactRationalLiteral (-140458099957425187) 102400000000000000000),
            (exactRationalLiteral (9338248482865139) 3200000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1337869858905259673) 983040000000000000000),
            (exactRationalLiteral (120184381819528307) 51200000000000000000),
            (exactRationalLiteral (-20558255076455651) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6325822380196331021) 409600000000000000000),
            (exactRationalLiteral (-229388124937651881) 12800000000000000000),
            (exactRationalLiteral (18609094812138873) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (159698126280213070663) 3276800000000000000000),
            (exactRationalLiteral (11513509219281018267) 102400000000000000000),
            (exactRationalLiteral (-206235033271853067) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-13435158396859865833) 1228800000000000000000),
            (exactRationalLiteral (-2683596057247957551) 12800000000000000000),
            (exactRationalLiteral (-679658948308921) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-185983779346307572477) 3276800000000000000000),
            (exactRationalLiteral (14651738312213518503) 102400000000000000000),
            (exactRationalLiteral (258575271533269161) 3200000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (156307205691186863351) 4915200000000000000000),
            (exactRationalLiteral (-985079625941972919) 51200000000000000000),
            (exactRationalLiteral (-109594178126070409) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (8297793413409033733) 4915200000000000000000),
            (exactRationalLiteral (-488105494906413749) 51200000000000000000),
            (exactRationalLiteral (28712087935671397) 1600000000000000000),
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
          (exactRationalLiteral (410413962845185263) 204800000000000000000),
          (exactRationalLiteral (3973094903345388203) 122880000000000000000),
          (exactRationalLiteral (75135436971520140223) 1228800000000000000000),
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
          (exactRationalLiteral (194765257363488521) 307200000000000000000),
          (exactRationalLiteral (8448566121418758383) 1228800000000000000000),
          (exactRationalLiteral (14505392961942058529) 614400000000000000000),
          (exactRationalLiteral (24070293367769421151) 307200000000000000000),
          (exactRationalLiteral (43289294348159927477) 614400000000000000000),
          (exactRationalLiteral (20788367105117627) 800000000000000000),
          (exactRationalLiteral (1768687376782573) 600000000000000000),
          (exactRationalLiteral (113784327655391265523) 614400000000000000000),
          (exactRationalLiteral (241847997434316991171) 614400000000000000000),
          (exactRationalLiteral (113784327655391265523) 614400000000000000000),
          (exactRationalLiteral (1768687376782573) 600000000000000000),
          (exactRationalLiteral (20788367105117627) 800000000000000000),
          (exactRationalLiteral (43289294348159927477) 614400000000000000000),
          (exactRationalLiteral (24070293367769421151) 307200000000000000000),
          (exactRationalLiteral (14505392961942058529) 614400000000000000000),
          (exactRationalLiteral (8448566121418758383) 1228800000000000000000),
          (exactRationalLiteral (194765257363488521) 307200000000000000000),
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
          (exactRationalLiteral (75135436971520140223) 1228800000000000000000),
          (exactRationalLiteral (3973094903345388203) 122880000000000000000),
          (exactRationalLiteral (410413962845185263) 204800000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (27, 56),
      (28, 8)
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
            (exactRationalLiteral (15200517142414269) 13107200000000000000),
            (exactRationalLiteral (-15200517142414269) 2048000000000000000),
            (exactRationalLiteral (5066839047471423) 320000000000000000),
            (exactRationalLiteral (-1688946349157141) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (149160525004574523017) 4915200000000000000000),
            (exactRationalLiteral (-1383992735170083511) 51200000000000000000),
            (exactRationalLiteral (-89862376487984887) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-93463331203532225173) 1966080000000000000000),
            (exactRationalLiteral (3099342768627444091) 20480000000000000000),
            (exactRationalLiteral (32782498785716363) 640000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9828338670159186573) 409600000000000000000),
            (exactRationalLiteral (-2656377374416313999) 12800000000000000000),
            (exactRationalLiteral (14289000364130697) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (545358708223686780619) 9830400000000000000000),
            (exactRationalLiteral (2103523263901090783) 20480000000000000000),
            (exactRationalLiteral (-291711416615929109) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-20113058425106207417) 1228800000000000000000),
            (exactRationalLiteral (-146237582007581161) 12800000000000000000),
            (exactRationalLiteral (22966176652896487) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (7145756270247517091) 4915200000000000000000),
            (exactRationalLiteral (28951234374464051) 51200000000000000000),
            (exactRationalLiteral (-25058318646076477) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1171845934540176401) 3276800000000000000000),
            (exactRationalLiteral (-98168169712377699) 102400000000000000000),
            (exactRationalLiteral (2361343327931721) 640000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (14990067055356143629) 3276800000000000000000),
            (exactRationalLiteral (49238928744164363) 20480000000000000000),
            (exactRationalLiteral (-2970076011913401) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (614978477664526593) 163840000000000000000),
            (exactRationalLiteral (59627807114322983) 25600000000000000000),
            (exactRationalLiteral (1611423288926271) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-148490336338804702571) 9830400000000000000000),
            (exactRationalLiteral (-445947038848490363) 102400000000000000000),
            (exactRationalLiteral (-7406124694205579) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-15685782582277556147) 2457600000000000000000),
            (exactRationalLiteral (-120886491251211083) 25600000000000000000),
            (exactRationalLiteral (-2063833083182051) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (29719129173249859411) 4915200000000000000000),
            (exactRationalLiteral (68472754108261751) 10240000000000000000),
            (exactRationalLiteral (5457746490987091) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-96697336510564379) 491520000000000000000),
            (exactRationalLiteral (109462684705563161) 25600000000000000000),
            (exactRationalLiteral (-3482884168701511) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-63151295237315294137) 9830400000000000000000),
            (exactRationalLiteral (443831532566655127) 102400000000000000000),
            (exactRationalLiteral (-2854653215867909) 640000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (107627794395477450823) 4915200000000000000000),
            (exactRationalLiteral (-862095205879627913) 51200000000000000000),
            (exactRationalLiteral (22812925055989159) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (178831468032931756433) 2457600000000000000000),
            (exactRationalLiteral (-290621995604861123) 5120000000000000000),
            (exactRationalLiteral (4691100355419229) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (-310148906937128951419) 4915200000000000000000),
            (exactRationalLiteral (3746653324566199653) 51200000000000000000),
            (exactRationalLiteral (-17384468207863487) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (-255479560045984261981) 9830400000000000000000),
            (exactRationalLiteral (36302988375553971) 102400000000000000000),
            (exactRationalLiteral (46022067980413379) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1539045326462541881) 491520000000000000000),
            (exactRationalLiteral (-29337587079371401) 5120000000000000000),
            (exactRationalLiteral (703510788754471) 160000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-863187577621557450797) 4915200000000000000000),
            (exactRationalLiteral (5068092633716822931) 51200000000000000000),
            (exactRationalLiteral (-53558125890471341) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1835608645908737969813) 4915200000000000000000),
            (exactRationalLiteral (-10689169003121180187) 51200000000000000000),
            (exactRationalLiteral (108019732243905077) 1600000000000000000),
            (exactRationalLiteral (-694811939776553) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-863187577621557450797) 4915200000000000000000),
            (exactRationalLiteral (5068092633716822931) 51200000000000000000),
            (exactRationalLiteral (-53558125890471341) 1600000000000000000),
            (exactRationalLiteral (1042241447353363) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1539045326462541881) 491520000000000000000),
            (exactRationalLiteral (-29337587079371401) 5120000000000000000),
            (exactRationalLiteral (703510788754471) 160000000000000000),
            (exactRationalLiteral (-22222996467439) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-255479560045984261981) 9830400000000000000000),
            (exactRationalLiteral (36302988375553971) 102400000000000000000),
            (exactRationalLiteral (46022067980413379) 3200000000000000000),
            (exactRationalLiteral (-2947819484283181) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-310148906937128951419) 4915200000000000000000),
            (exactRationalLiteral (3746653324566199653) 51200000000000000000),
            (exactRationalLiteral (-17384468207863487) 320000000000000000),
            (exactRationalLiteral (146169954063853) 6000000000000000)
          ],
          ![
            (exactRationalLiteral (178831468032931756433) 2457600000000000000000),
            (exactRationalLiteral (-290621995604861123) 5120000000000000000),
            (exactRationalLiteral (4691100355419229) 160000000000000000),
            (exactRationalLiteral (-29023050404839) 3000000000000000)
          ],
          ![
            (exactRationalLiteral (107627794395477450823) 4915200000000000000000),
            (exactRationalLiteral (-862095205879627913) 51200000000000000000),
            (exactRationalLiteral (22812925055989159) 1600000000000000000),
            (exactRationalLiteral (-500536674452579) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (-63151295237315294137) 9830400000000000000000),
            (exactRationalLiteral (443831532566655127) 102400000000000000000),
            (exactRationalLiteral (-2854653215867909) 640000000000000000),
            (exactRationalLiteral (708293293737149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-96697336510564379) 491520000000000000000),
            (exactRationalLiteral (109462684705563161) 25600000000000000000),
            (exactRationalLiteral (-3482884168701511) 800000000000000000),
            (exactRationalLiteral (-56378500616333) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (29719129173249859411) 4915200000000000000000),
            (exactRationalLiteral (68472754108261751) 10240000000000000000),
            (exactRationalLiteral (5457746490987091) 1600000000000000000),
            (exactRationalLiteral (253127137092691) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-15685782582277556147) 2457600000000000000000),
            (exactRationalLiteral (-120886491251211083) 25600000000000000000),
            (exactRationalLiteral (-2063833083182051) 800000000000000000),
            (exactRationalLiteral (-879969698171) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-148490336338804702571) 9830400000000000000000),
            (exactRationalLiteral (-445947038848490363) 102400000000000000000),
            (exactRationalLiteral (-7406124694205579) 3200000000000000000),
            (exactRationalLiteral (-463561827817627) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (614978477664526593) 163840000000000000000),
            (exactRationalLiteral (59627807114322983) 25600000000000000000),
            (exactRationalLiteral (1611423288926271) 800000000000000000),
            (exactRationalLiteral (120877376518999) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (14990067055356143629) 3276800000000000000000),
            (exactRationalLiteral (49238928744164363) 20480000000000000000),
            (exactRationalLiteral (-2970076011913401) 3200000000000000000),
            (exactRationalLiteral (-481007783898793) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-1171845934540176401) 3276800000000000000000),
            (exactRationalLiteral (-98168169712377699) 102400000000000000000),
            (exactRationalLiteral (2361343327931721) 640000000000000000),
            (exactRationalLiteral (1234234078396733) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7145756270247517091) 4915200000000000000000),
            (exactRationalLiteral (28951234374464051) 51200000000000000000),
            (exactRationalLiteral (-25058318646076477) 1600000000000000000),
            (exactRationalLiteral (-2250031784810413) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20113058425106207417) 1228800000000000000000),
            (exactRationalLiteral (-146237582007581161) 12800000000000000000),
            (exactRationalLiteral (22966176652896487) 400000000000000000),
            (exactRationalLiteral (2178540920378807) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (545358708223686780619) 9830400000000000000000),
            (exactRationalLiteral (2103523263901090783) 20480000000000000000),
            (exactRationalLiteral (-291711416615929109) 3200000000000000000),
            (exactRationalLiteral (-42738191672038021) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9828338670159186573) 409600000000000000000),
            (exactRationalLiteral (-2656377374416313999) 12800000000000000000),
            (exactRationalLiteral (14289000364130697) 400000000000000000),
            (exactRationalLiteral (7484329656219809) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-93463331203532225173) 1966080000000000000000),
            (exactRationalLiteral (3099342768627444091) 20480000000000000000),
            (exactRationalLiteral (32782498785716363) 640000000000000000),
            (exactRationalLiteral (-47331388802343673) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (149160525004574523017) 4915200000000000000000),
            (exactRationalLiteral (-1383992735170083511) 51200000000000000000),
            (exactRationalLiteral (-89862376487984887) 1600000000000000000),
            (exactRationalLiteral (3288633606347587) 50000000000000000)
          ],
          ![
            (exactRationalLiteral (15200517142414269) 13107200000000000000),
            (exactRationalLiteral (-15200517142414269) 2048000000000000000),
            (exactRationalLiteral (5066839047471423) 320000000000000000),
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
          (exactRationalLiteral (4675474600372236227) 153600000000000000000),
          (exactRationalLiteral (23999736864195138209) 409600000000000000000),
          (exactRationalLiteral (853362254177078443) 51200000000000000000),
          (exactRationalLiteral (37510499245067021) 25600000000000000000),
          (exactRationalLiteral (471673491095036219) 1228800000000000000000),
          (exactRationalLiteral (5712424232676407167) 1228800000000000000000),
          (exactRationalLiteral (1176064466694270707) 307200000000000000000),
          (exactRationalLiteral (6243785807969192001) 409600000000000000000),
          (exactRationalLiteral (401365860881260843) 61440000000000000000),
          (exactRationalLiteral (769071171287095991) 122880000000000000000),
          (exactRationalLiteral (100360626669161) 300000000000000000),
          (exactRationalLiteral (630153657354829) 96000000000000000),
          (exactRationalLiteral (26924809667555581) 1200000000000000000),
          (exactRationalLiteral (1864236348964397) 25000000000000000),
          (exactRationalLiteral (39264317405126599) 600000000000000000),
          (exactRationalLiteral (499150064300438501) 19200000000000000000),
          (exactRationalLiteral (1015600555707670709) 307200000000000000000),
          (exactRationalLiteral (17874218183224013) 100000000000000000),
          (exactRationalLiteral (456055248181311659) 1200000000000000000),
          (exactRationalLiteral (17874218183224013) 100000000000000000),
          (exactRationalLiteral (1015600555707670709) 307200000000000000000),
          (exactRationalLiteral (499150064300438501) 19200000000000000000),
          (exactRationalLiteral (39264317405126599) 600000000000000000),
          (exactRationalLiteral (1864236348964397) 25000000000000000),
          (exactRationalLiteral (26924809667555581) 1200000000000000000),
          (exactRationalLiteral (630153657354829) 96000000000000000),
          (exactRationalLiteral (100360626669161) 300000000000000000),
          (exactRationalLiteral (769071171287095991) 122880000000000000000),
          (exactRationalLiteral (401365860881260843) 61440000000000000000),
          (exactRationalLiteral (6243785807969192001) 409600000000000000000),
          (exactRationalLiteral (1176064466694270707) 307200000000000000000),
          (exactRationalLiteral (5712424232676407167) 1228800000000000000000),
          (exactRationalLiteral (471673491095036219) 1228800000000000000000),
          (exactRationalLiteral (37510499245067021) 25600000000000000000),
          (exactRationalLiteral (853362254177078443) 51200000000000000000),
          (exactRationalLiteral (23999736864195138209) 409600000000000000000),
          (exactRationalLiteral (4675474600372236227) 153600000000000000000),
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
      (27, 55),
      (28, 7)
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
theorem generatorCoordinates27_valid : ∀ i, (generatorCoordinates27 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
