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

/-- Actual coordinate interval candidates, block 24. -/
def generatorCoordinates24 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 5
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
            (exactRationalLiteral (2745191161656999) 2621440000000000000),
            (exactRationalLiteral (-2745191161656999) 409600000000000000),
            (exactRationalLiteral (915063720552333) 64000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (278325652538572739711) 9830400000000000000000),
            (exactRationalLiteral (-2636611565342184913) 102400000000000000000),
            (exactRationalLiteral (-162915936861499681) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-104877723795960295307) 2457600000000000000000),
            (exactRationalLiteral (3649481451491713773) 25600000000000000000),
            (exactRationalLiteral (36245028510567013) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-83772855326171998417) 3276800000000000000000),
            (exactRationalLiteral (-20073593858993102307) 102400000000000000000),
            (exactRationalLiteral (119354666076990381) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (133562886752222294239) 2457600000000000000000),
            (exactRationalLiteral (2505502140626976543) 25600000000000000000),
            (exactRationalLiteral (-71708550611817377) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-6731255534966761909) 409600000000000000000),
            (exactRationalLiteral (-142717934025475911) 12800000000000000000),
            (exactRationalLiteral (22530357802509201) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2990654285578115311) 1638400000000000000000),
            (exactRationalLiteral (18591933943303581) 51200000000000000000),
            (exactRationalLiteral (-24293856213137043) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3294029092520864861) 1966080000000000000000),
            (exactRationalLiteral (-95844887108767841) 102400000000000000000),
            (exactRationalLiteral (10761866753297423) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (7121433596552610017) 9830400000000000000000),
            (exactRationalLiteral (50992603517206673) 102400000000000000000),
            (exactRationalLiteral (-3751103328335551) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (25726906873274473049) 9830400000000000000000),
            (exactRationalLiteral (93474074423765097) 102400000000000000000),
            (exactRationalLiteral (487814125864933) 640000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9977107136299924739) 4915200000000000000000),
            (exactRationalLiteral (18809702302061991) 10240000000000000000),
            (exactRationalLiteral (-79852929584509) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-19200464571961749) 1638400000000000000),
            (exactRationalLiteral (-3948241513182851) 1280000000000000000),
            (exactRationalLiteral (-3227540351763) 8000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-20400265568811333671) 4915200000000000000000),
            (exactRationalLiteral (-4978795426469671) 51200000000000000000),
            (exactRationalLiteral (-2366396797048103) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1193674535075545759) 983040000000000000000),
            (exactRationalLiteral (41861526273083903) 10240000000000000000),
            (exactRationalLiteral (221848246396379) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-33547835040323696447) 4915200000000000000000),
            (exactRationalLiteral (401655043779759153) 51200000000000000000),
            (exactRationalLiteral (-1695096789839711) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-41577187678549281173) 1966080000000000000000),
            (exactRationalLiteral (555323227811174107) 20480000000000000000),
            (exactRationalLiteral (-31830660881503369) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (47319528418915792187) 983040000000000000000),
            (exactRationalLiteral (1012052598800596023) 51200000000000000000),
            (exactRationalLiteral (-253923799008686777) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (525563796999274598713) 2457600000000000000000),
            (exactRationalLiteral (-2224820926092814619) 5120000000000000000),
            (exactRationalLiteral (108359487731416613) 160000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-888643079636202808143) 3276800000000000000000),
            (exactRationalLiteral (62952485992491445411) 102400000000000000000),
            (exactRationalLiteral (-114573245789251029) 128000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (69167629909303101931) 2457600000000000000000),
            (exactRationalLiteral (-6442939543076364501) 25600000000000000000),
            (exactRationalLiteral (365822767169845099) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (31092454717720704239) 9830400000000000000000),
            (exactRationalLiteral (1334141373910741343) 102400000000000000000),
            (exactRationalLiteral (-183693693961132849) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-3125903249615898614393) 9830400000000000000000),
            (exactRationalLiteral (21065392381216851159) 102400000000000000000),
            (exactRationalLiteral (-303103472119770329) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3282898816279941611921) 4915200000000000000000),
            (exactRationalLiteral (-21136263191757988031) 51200000000000000000),
            (exactRationalLiteral (53602589639601661) 320000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-3125903249615898614393) 9830400000000000000000),
            (exactRationalLiteral (21065392381216851159) 102400000000000000000),
            (exactRationalLiteral (-303103472119770329) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (31092454717720704239) 9830400000000000000000),
            (exactRationalLiteral (1334141373910741343) 102400000000000000000),
            (exactRationalLiteral (-183693693961132849) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (69167629909303101931) 2457600000000000000000),
            (exactRationalLiteral (-6442939543076364501) 25600000000000000000),
            (exactRationalLiteral (365822767169845099) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-888643079636202808143) 3276800000000000000000),
            (exactRationalLiteral (62952485992491445411) 102400000000000000000),
            (exactRationalLiteral (-114573245789251029) 128000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (525563796999274598713) 2457600000000000000000),
            (exactRationalLiteral (-2224820926092814619) 5120000000000000000),
            (exactRationalLiteral (108359487731416613) 160000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (47319528418915792187) 983040000000000000000),
            (exactRationalLiteral (1012052598800596023) 51200000000000000000),
            (exactRationalLiteral (-253923799008686777) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-41577187678549281173) 1966080000000000000000),
            (exactRationalLiteral (555323227811174107) 20480000000000000000),
            (exactRationalLiteral (-31830660881503369) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-33547835040323696447) 4915200000000000000000),
            (exactRationalLiteral (401655043779759153) 51200000000000000000),
            (exactRationalLiteral (-1695096789839711) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1193674535075545759) 983040000000000000000),
            (exactRationalLiteral (41861526273083903) 10240000000000000000),
            (exactRationalLiteral (221848246396379) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20400265568811333671) 4915200000000000000000),
            (exactRationalLiteral (-4978795426469671) 51200000000000000000),
            (exactRationalLiteral (-2366396797048103) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-19200464571961749) 1638400000000000000),
            (exactRationalLiteral (-3948241513182851) 1280000000000000000),
            (exactRationalLiteral (-3227540351763) 8000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (9977107136299924739) 4915200000000000000000),
            (exactRationalLiteral (18809702302061991) 10240000000000000000),
            (exactRationalLiteral (-79852929584509) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (25726906873274473049) 9830400000000000000000),
            (exactRationalLiteral (93474074423765097) 102400000000000000000),
            (exactRationalLiteral (487814125864933) 640000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7121433596552610017) 9830400000000000000000),
            (exactRationalLiteral (50992603517206673) 102400000000000000000),
            (exactRationalLiteral (-3751103328335551) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3294029092520864861) 1966080000000000000000),
            (exactRationalLiteral (-95844887108767841) 102400000000000000000),
            (exactRationalLiteral (10761866753297423) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2990654285578115311) 1638400000000000000000),
            (exactRationalLiteral (18591933943303581) 51200000000000000000),
            (exactRationalLiteral (-24293856213137043) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6731255534966761909) 409600000000000000000),
            (exactRationalLiteral (-142717934025475911) 12800000000000000000),
            (exactRationalLiteral (22530357802509201) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (133562886752222294239) 2457600000000000000000),
            (exactRationalLiteral (2505502140626976543) 25600000000000000000),
            (exactRationalLiteral (-71708550611817377) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-83772855326171998417) 3276800000000000000000),
            (exactRationalLiteral (-20073593858993102307) 102400000000000000000),
            (exactRationalLiteral (119354666076990381) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-104877723795960295307) 2457600000000000000000),
            (exactRationalLiteral (3649481451491713773) 25600000000000000000),
            (exactRationalLiteral (36245028510567013) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (278325652538572739711) 9830400000000000000000),
            (exactRationalLiteral (-2636611565342184913) 102400000000000000000),
            (exactRationalLiteral (-162915936861499681) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2745191161656999) 2621440000000000000),
            (exactRationalLiteral (-2745191161656999) 409600000000000000),
            (exactRationalLiteral (915063720552333) 64000000000000000),
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
          (exactRationalLiteral (12963527949781870921) 409600000000000000000),
          (exactRationalLiteral (17606748601475376511) 307200000000000000000),
          (exactRationalLiteral (513805192718523679) 30720000000000000000),
          (exactRationalLiteral (140890324919919619) 76800000000000000000),
          (exactRationalLiteral (2090544127320191081) 1228800000000000000000),
          (exactRationalLiteral (907849560811863337) 1228800000000000000000),
          (exactRationalLiteral (1083951285033864379) 409600000000000000000),
          (exactRationalLiteral (1282369912911144227) 614400000000000000000),
          (exactRationalLiteral (907454068337410421) 76800000000000000000),
          (exactRationalLiteral (2552802071105232359) 614400000000000000000),
          (exactRationalLiteral (274875970694754617) 204800000000000000000),
          (exactRationalLiteral (2828606563943157) 400000000000000000),
          (exactRationalLiteral (52810068625084627) 2400000000000000000),
          (exactRationalLiteral (9953840809732728021) 204800000000000000000),
          (exactRationalLiteral (68432035768554923) 300000000000000000),
          (exactRationalLiteral (699109075468845169) 2400000000000000000),
          (exactRationalLiteral (273488472822671) 7500000000000000),
          (exactRationalLiteral (1439886843790440349) 409600000000000000000),
          (exactRationalLiteral (259604446661511263) 800000000000000000),
          (exactRationalLiteral (817167956189846509) 1200000000000000000),
          (exactRationalLiteral (259604446661511263) 800000000000000000),
          (exactRationalLiteral (1439886843790440349) 409600000000000000000),
          (exactRationalLiteral (273488472822671) 7500000000000000),
          (exactRationalLiteral (699109075468845169) 2400000000000000000),
          (exactRationalLiteral (68432035768554923) 300000000000000000),
          (exactRationalLiteral (9953840809732728021) 204800000000000000000),
          (exactRationalLiteral (52810068625084627) 2400000000000000000),
          (exactRationalLiteral (2828606563943157) 400000000000000000),
          (exactRationalLiteral (274875970694754617) 204800000000000000000),
          (exactRationalLiteral (2552802071105232359) 614400000000000000000),
          (exactRationalLiteral (907454068337410421) 76800000000000000000),
          (exactRationalLiteral (1282369912911144227) 614400000000000000000),
          (exactRationalLiteral (1083951285033864379) 409600000000000000000),
          (exactRationalLiteral (907849560811863337) 1228800000000000000000),
          (exactRationalLiteral (2090544127320191081) 1228800000000000000000),
          (exactRationalLiteral (140890324919919619) 76800000000000000000),
          (exactRationalLiteral (513805192718523679) 30720000000000000000),
          (exactRationalLiteral (17606748601475376511) 307200000000000000000),
          (exactRationalLiteral (12963527949781870921) 409600000000000000000),
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
      (28, 7),
      (28, 23)
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
            (exactRationalLiteral (223377221561497289) 327680000000000000000),
            (exactRationalLiteral (-51548589591114759) 10240000000000000000),
            (exactRationalLiteral (3965276122393443) 320000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (260695529772558997637) 9830400000000000000000),
            (exactRationalLiteral (-3216006378599501849) 102400000000000000000),
            (exactRationalLiteral (-126781469767158787) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-82633914144198634073) 2457600000000000000000),
            (exactRationalLiteral (750090373175253809) 5120000000000000000),
            (exactRationalLiteral (14240178681710623) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-123291657013185097707) 3276800000000000000000),
            (exactRationalLiteral (-19369724144687425083) 102400000000000000000),
            (exactRationalLiteral (232580191075848231) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (49217722434974755927) 819200000000000000000),
            (exactRationalLiteral (2177553096320668439) 25600000000000000000),
            (exactRationalLiteral (-3690638861653467) 32000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-4152547383359424241) 245760000000000000000),
            (exactRationalLiteral (-44110003502484319) 12800000000000000000),
            (exactRationalLiteral (5354721491797319) 80000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (8774931001963970431) 4915200000000000000000),
            (exactRationalLiteral (-87112082845520827) 51200000000000000000),
            (exactRationalLiteral (-28558152181275161) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-16907740343343706987) 9830400000000000000000),
            (exactRationalLiteral (-9726279931750101) 20480000000000000000),
            (exactRationalLiteral (2568975394342249) 640000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (7379483092721289947) 9830400000000000000000),
            (exactRationalLiteral (34541747706597721) 102400000000000000000),
            (exactRationalLiteral (-178972983078757) 128000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (26318496426400981699) 9830400000000000000000),
            (exactRationalLiteral (103968486457074801) 102400000000000000000),
            (exactRationalLiteral (2808135387330187) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3513336500061064091) 1638400000000000000000),
            (exactRationalLiteral (748110918241463) 409600000000000000),
            (exactRationalLiteral (-187470435479031) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7319530873902690329) 614400000000000000000),
            (exactRationalLiteral (-20034537559100567) 6400000000000000000),
            (exactRationalLiteral (-65976487799081) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-1363963899320966931) 327680000000000000000),
            (exactRationalLiteral (-14906076054549599) 51200000000000000000),
            (exactRationalLiteral (-2597243516991861) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (7227378102214477081) 4915200000000000000000),
            (exactRationalLiteral (42088750838948471) 10240000000000000000),
            (exactRationalLiteral (346213168265041) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2077199331567670443) 327680000000000000000),
            (exactRationalLiteral (395002639424481017) 51200000000000000000),
            (exactRationalLiteral (-1631105387799357) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-191618111122684386163) 9830400000000000000000),
            (exactRationalLiteral (2644342678682275519) 102400000000000000000),
            (exactRationalLiteral (-34306069305294139) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (239784079616324566397) 4915200000000000000000),
            (exactRationalLiteral (76961161288984239) 51200000000000000000),
            (exactRationalLiteral (-42724383949423823) 320000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (465050868005464260739) 2457600000000000000000),
            (exactRationalLiteral (-9091850113291188927) 25600000000000000000),
            (exactRationalLiteral (474329819929359019) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-2321217634289529265567) 9830400000000000000000),
            (exactRationalLiteral (52179492614019240059) 102400000000000000000),
            (exactRationalLiteral (-2522165544504826951) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (34717578380954235721) 2457600000000000000000),
            (exactRationalLiteral (-5070792212361394301) 25600000000000000000),
            (exactRationalLiteral (320250898187640001) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (37000870580859867349) 9830400000000000000000),
            (exactRationalLiteral (653312571670364567) 102400000000000000000),
            (exactRationalLiteral (-156720707159055539) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-1001020836596033128097) 3276800000000000000000),
            (exactRationalLiteral (19895792095705453391) 102400000000000000000),
            (exactRationalLiteral (-56339334127185711) 640000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (631846192335471236783) 983040000000000000000),
            (exactRationalLiteral (-20097426814172754551) 51200000000000000000),
            (exactRationalLiteral (50281048118921687) 320000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-1001020836596033128097) 3276800000000000000000),
            (exactRationalLiteral (19895792095705453391) 102400000000000000000),
            (exactRationalLiteral (-56339334127185711) 640000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (37000870580859867349) 9830400000000000000000),
            (exactRationalLiteral (653312571670364567) 102400000000000000000),
            (exactRationalLiteral (-156720707159055539) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (34717578380954235721) 2457600000000000000000),
            (exactRationalLiteral (-5070792212361394301) 25600000000000000000),
            (exactRationalLiteral (320250898187640001) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-2321217634289529265567) 9830400000000000000000),
            (exactRationalLiteral (52179492614019240059) 102400000000000000000),
            (exactRationalLiteral (-2522165544504826951) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (465050868005464260739) 2457600000000000000000),
            (exactRationalLiteral (-9091850113291188927) 25600000000000000000),
            (exactRationalLiteral (474329819929359019) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (239784079616324566397) 4915200000000000000000),
            (exactRationalLiteral (76961161288984239) 51200000000000000000),
            (exactRationalLiteral (-42724383949423823) 320000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-191618111122684386163) 9830400000000000000000),
            (exactRationalLiteral (2644342678682275519) 102400000000000000000),
            (exactRationalLiteral (-34306069305294139) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-2077199331567670443) 327680000000000000000),
            (exactRationalLiteral (395002639424481017) 51200000000000000000),
            (exactRationalLiteral (-1631105387799357) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (7227378102214477081) 4915200000000000000000),
            (exactRationalLiteral (42088750838948471) 10240000000000000000),
            (exactRationalLiteral (346213168265041) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1363963899320966931) 327680000000000000000),
            (exactRationalLiteral (-14906076054549599) 51200000000000000000),
            (exactRationalLiteral (-2597243516991861) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7319530873902690329) 614400000000000000000),
            (exactRationalLiteral (-20034537559100567) 6400000000000000000),
            (exactRationalLiteral (-65976487799081) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (3513336500061064091) 1638400000000000000000),
            (exactRationalLiteral (748110918241463) 409600000000000000),
            (exactRationalLiteral (-187470435479031) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (26318496426400981699) 9830400000000000000000),
            (exactRationalLiteral (103968486457074801) 102400000000000000000),
            (exactRationalLiteral (2808135387330187) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7379483092721289947) 9830400000000000000000),
            (exactRationalLiteral (34541747706597721) 102400000000000000000),
            (exactRationalLiteral (-178972983078757) 128000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-16907740343343706987) 9830400000000000000000),
            (exactRationalLiteral (-9726279931750101) 20480000000000000000),
            (exactRationalLiteral (2568975394342249) 640000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (8774931001963970431) 4915200000000000000000),
            (exactRationalLiteral (-87112082845520827) 51200000000000000000),
            (exactRationalLiteral (-28558152181275161) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4152547383359424241) 245760000000000000000),
            (exactRationalLiteral (-44110003502484319) 12800000000000000000),
            (exactRationalLiteral (5354721491797319) 80000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (49217722434974755927) 819200000000000000000),
            (exactRationalLiteral (2177553096320668439) 25600000000000000000),
            (exactRationalLiteral (-3690638861653467) 32000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-123291657013185097707) 3276800000000000000000),
            (exactRationalLiteral (-19369724144687425083) 102400000000000000000),
            (exactRationalLiteral (232580191075848231) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-82633914144198634073) 2457600000000000000000),
            (exactRationalLiteral (750090373175253809) 5120000000000000000),
            (exactRationalLiteral (14240178681710623) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (260695529772558997637) 9830400000000000000000),
            (exactRationalLiteral (-3216006378599501849) 102400000000000000000),
            (exactRationalLiteral (-126781469767158787) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (223377221561497289) 327680000000000000000),
            (exactRationalLiteral (-51548589591114759) 10240000000000000000),
            (exactRationalLiteral (3965276122393443) 320000000000000000),
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
          (exactRationalLiteral (34874095127716691) 40960000000000000000),
          (exactRationalLiteral (33743142158188607047) 1228800000000000000000),
          (exactRationalLiteral (11728943347608485143) 307200000000000000000),
          (exactRationalLiteral (2225155156968180181) 51200000000000000000),
          (exactRationalLiteral (2404667968262460991) 38400000000000000000),
          (exactRationalLiteral (217038980756112821) 12800000000000000000),
          (exactRationalLiteral (1119090617742597061) 614400000000000000000),
          (exactRationalLiteral (265844662598369029) 153600000000000000000),
          (exactRationalLiteral (116708183616966557) 153600000000000000000),
          (exactRationalLiteral (416234544129893741) 153600000000000000000),
          (exactRationalLiteral (169061482413505571) 76800000000000000000),
          (exactRationalLiteral (19218294427168989) 1600000000000000000),
          (exactRationalLiteral (320501310498267191) 76800000000000000000),
          (exactRationalLiteral (4912381366727771) 3072000000000000000),
          (exactRationalLiteral (4043490400456614743) 614400000000000000000),
          (exactRationalLiteral (24956602457804399969) 1228800000000000000000),
          (exactRationalLiteral (1500340698485811787) 30720000000000000000),
          (exactRationalLiteral (2468915708072448833) 12288000000000000000),
          (exactRationalLiteral (310686711445651836373) 1228800000000000000000),
          (exactRationalLiteral (6364186705886555147) 307200000000000000000),
          (exactRationalLiteral (601627072934294267) 153600000000000000000),
          (exactRationalLiteral (382950709935983181377) 1228800000000000000000),
          (exactRationalLiteral (134178573403977498867) 204800000000000000000),
          (exactRationalLiteral (382950709935983181377) 1228800000000000000000),
          (exactRationalLiteral (601627072934294267) 153600000000000000000),
          (exactRationalLiteral (6364186705886555147) 307200000000000000000),
          (exactRationalLiteral (310686711445651836373) 1228800000000000000000),
          (exactRationalLiteral (2468915708072448833) 12288000000000000000),
          (exactRationalLiteral (1500340698485811787) 30720000000000000000),
          (exactRationalLiteral (24956602457804399969) 1228800000000000000000),
          (exactRationalLiteral (4043490400456614743) 614400000000000000000),
          (exactRationalLiteral (4912381366727771) 3072000000000000000),
          (exactRationalLiteral (320501310498267191) 76800000000000000000),
          (exactRationalLiteral (19218294427168989) 1600000000000000000),
          (exactRationalLiteral (169061482413505571) 76800000000000000000),
          (exactRationalLiteral (416234544129893741) 153600000000000000000),
          (exactRationalLiteral (116708183616966557) 153600000000000000000),
          (exactRationalLiteral (265844662598369029) 153600000000000000000),
          (exactRationalLiteral (1119090617742597061) 614400000000000000000),
          (exactRationalLiteral (217038980756112821) 12800000000000000000),
          (exactRationalLiteral (2404667968262460991) 38400000000000000000),
          (exactRationalLiteral (2225155156968180181) 51200000000000000000),
          (exactRationalLiteral (11728943347608485143) 307200000000000000000),
          (exactRationalLiteral (33743142158188607047) 1228800000000000000000),
          (exactRationalLiteral (34874095127716691) 40960000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 6),
      (28, 22)
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
            (exactRationalLiteral (135327756895017247) 327680000000000000000),
            (exactRationalLiteral (-36907570062277431) 10240000000000000000),
            (exactRationalLiteral (3355233642025221) 320000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (9600906069285337787) 393216000000000000000),
            (exactRationalLiteral (-3650863323479455209) 102400000000000000000),
            (exactRationalLiteral (-90647002672817893) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-60048340204075917887) 2457600000000000000000),
            (exactRationalLiteral (3763402880945398757) 25600000000000000000),
            (exactRationalLiteral (-7764671147145767) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-160949817171591411149) 3276800000000000000000),
            (exactRationalLiteral (-18212952330386316459) 102400000000000000000),
            (exactRationalLiteral (345805716074706081) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (159529064540634161123) 2457600000000000000000),
            (exactRationalLiteral (1767374368296283143) 25600000000000000000),
            (exactRationalLiteral (-112823392470855973) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-20689140649678278403) 1228800000000000000000),
            (exactRationalLiteral (71470925646416849) 12800000000000000000),
            (exactRationalLiteral (31016857115463989) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1578500698968598213) 983040000000000000000),
            (exactRationalLiteral (-209873283506897707) 51200000000000000000),
            (exactRationalLiteral (-32822448149413279) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-17037058176762019789) 9830400000000000000000),
            (exactRationalLiteral (6914128664922119) 102400000000000000000),
            (exactRationalLiteral (14927887190125067) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (7530148799042715677) 9830400000000000000000),
            (exactRationalLiteral (15198006901455273) 102400000000000000000),
            (exactRationalLiteral (-5197545825602299) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (8992493742941138279) 3276800000000000000000),
            (exactRationalLiteral (115939157522406593) 102400000000000000000),
            (exactRationalLiteral (3177200145335709) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (11098412573614963063) 4915200000000000000000),
            (exactRationalLiteral (92548748026477707) 51200000000000000000),
            (exactRationalLiteral (-295087941373553) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7440470969026902727) 614400000000000000000),
            (exactRationalLiteral (-20269019468306903) 6400000000000000000),
            (exactRationalLiteral (-51264466804087) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-20580985255225478923) 4915200000000000000000),
            (exactRationalLiteral (-25756743562404559) 51200000000000000000),
            (exactRationalLiteral (-2828090236935619) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2831564215029862117) 1638400000000000000000),
            (exactRationalLiteral (212077336711539843) 51200000000000000000),
            (exactRationalLiteral (470578090133703) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-28807291436013601411) 4915200000000000000000),
            (exactRationalLiteral (388606200677364297) 51200000000000000000),
            (exactRationalLiteral (-1567113985759003) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-176173629515949425797) 9830400000000000000000),
            (exactRationalLiteral (2502167584613517423) 102400000000000000000),
            (exactRationalLiteral (-36781477729084909) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (79281197021379771033) 1638400000000000000000),
            (exactRationalLiteral (-696922759176356897) 51200000000000000000),
            (exactRationalLiteral (-173320040485551453) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (415921854689958539221) 2457600000000000000000),
            (exactRationalLiteral (-7329466071029200943) 25600000000000000000),
            (exactRationalLiteral (406862201201634973) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-2037038002738565953529) 9830400000000000000000),
            (exactRationalLiteral (42775161636452829803) 102400000000000000000),
            (exactRationalLiteral (-2179999944278378177) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1590709681821745907) 491520000000000000000),
            (exactRationalLiteral (-3880932357575244493) 25600000000000000000),
            (exactRationalLiteral (274679029205434903) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (13049329824060565841) 3276800000000000000000),
            (exactRationalLiteral (80375716638297031) 102400000000000000000),
            (exactRationalLiteral (-129747720356978229) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-2886982490055562439509) 9830400000000000000000),
            (exactRationalLiteral (18811819016129422719) 102400000000000000000),
            (exactRationalLiteral (-260289869152086781) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1013865610949680452783) 1638400000000000000000),
            (exactRationalLiteral (-19125021267001120551) 51200000000000000000),
            (exactRationalLiteral (46959506598241713) 320000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2886982490055562439509) 9830400000000000000000),
            (exactRationalLiteral (18811819016129422719) 102400000000000000000),
            (exactRationalLiteral (-260289869152086781) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (13049329824060565841) 3276800000000000000000),
            (exactRationalLiteral (80375716638297031) 102400000000000000000),
            (exactRationalLiteral (-129747720356978229) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (1590709681821745907) 491520000000000000000),
            (exactRationalLiteral (-3880932357575244493) 25600000000000000000),
            (exactRationalLiteral (274679029205434903) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-2037038002738565953529) 9830400000000000000000),
            (exactRationalLiteral (42775161636452829803) 102400000000000000000),
            (exactRationalLiteral (-2179999944278378177) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (415921854689958539221) 2457600000000000000000),
            (exactRationalLiteral (-7329466071029200943) 25600000000000000000),
            (exactRationalLiteral (406862201201634973) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (79281197021379771033) 1638400000000000000000),
            (exactRationalLiteral (-696922759176356897) 51200000000000000000),
            (exactRationalLiteral (-173320040485551453) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-176173629515949425797) 9830400000000000000000),
            (exactRationalLiteral (2502167584613517423) 102400000000000000000),
            (exactRationalLiteral (-36781477729084909) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-28807291436013601411) 4915200000000000000000),
            (exactRationalLiteral (388606200677364297) 51200000000000000000),
            (exactRationalLiteral (-1567113985759003) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2831564215029862117) 1638400000000000000000),
            (exactRationalLiteral (212077336711539843) 51200000000000000000),
            (exactRationalLiteral (470578090133703) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20580985255225478923) 4915200000000000000000),
            (exactRationalLiteral (-25756743562404559) 51200000000000000000),
            (exactRationalLiteral (-2828090236935619) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7440470969026902727) 614400000000000000000),
            (exactRationalLiteral (-20269019468306903) 6400000000000000000),
            (exactRationalLiteral (-51264466804087) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (11098412573614963063) 4915200000000000000000),
            (exactRationalLiteral (92548748026477707) 51200000000000000000),
            (exactRationalLiteral (-295087941373553) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (8992493742941138279) 3276800000000000000000),
            (exactRationalLiteral (115939157522406593) 102400000000000000000),
            (exactRationalLiteral (3177200145335709) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7530148799042715677) 9830400000000000000000),
            (exactRationalLiteral (15198006901455273) 102400000000000000000),
            (exactRationalLiteral (-5197545825602299) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-17037058176762019789) 9830400000000000000000),
            (exactRationalLiteral (6914128664922119) 102400000000000000000),
            (exactRationalLiteral (14927887190125067) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1578500698968598213) 983040000000000000000),
            (exactRationalLiteral (-209873283506897707) 51200000000000000000),
            (exactRationalLiteral (-32822448149413279) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20689140649678278403) 1228800000000000000000),
            (exactRationalLiteral (71470925646416849) 12800000000000000000),
            (exactRationalLiteral (31016857115463989) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (159529064540634161123) 2457600000000000000000),
            (exactRationalLiteral (1767374368296283143) 25600000000000000000),
            (exactRationalLiteral (-112823392470855973) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-160949817171591411149) 3276800000000000000000),
            (exactRationalLiteral (-18212952330386316459) 102400000000000000000),
            (exactRationalLiteral (345805716074706081) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-60048340204075917887) 2457600000000000000000),
            (exactRationalLiteral (3763402880945398757) 25600000000000000000),
            (exactRationalLiteral (-7764671147145767) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (9600906069285337787) 393216000000000000000),
            (exactRationalLiteral (-3650863323479455209) 102400000000000000000),
            (exactRationalLiteral (-90647002672817893) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (135327756895017247) 327680000000000000000),
            (exactRationalLiteral (-36907570062277431) 10240000000000000000),
            (exactRationalLiteral (3355233642025221) 320000000000000000),
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
          (exactRationalLiteral (2745191161656999) 5120000000000000000),
          (exactRationalLiteral (3916956772828221659) 153600000000000000000),
          (exactRationalLiteral (1114856881803736301) 38400000000000000000),
          (exactRationalLiteral (22349761608133734819) 409600000000000000000),
          (exactRationalLiteral (6853434948235236791) 102400000000000000000),
          (exactRationalLiteral (21679817166770183) 1280000000000000000),
          (exactRationalLiteral (43884313275518299) 25600000000000000000),
          (exactRationalLiteral (533058083984620627) 307200000000000000000),
          (exactRationalLiteral (944973571455744739) 1228800000000000000000),
          (exactRationalLiteral (3416876854275705563) 1228800000000000000000),
          (exactRationalLiteral (473963322713222011) 204800000000000000000),
          (exactRationalLiteral (37507122324108691) 3072000000000000000),
          (exactRationalLiteral (861118965832644639) 204800000000000000000),
          (exactRationalLiteral (228309964298888533) 122880000000000000000),
          (exactRationalLiteral (468403802745374867) 76800000000000000000),
          (exactRationalLiteral (2871706859355708397) 153600000000000000000),
          (exactRationalLiteral (149621405175363091) 3072000000000000000),
          (exactRationalLiteral (6861946458062732953) 38400000000000000000),
          (exactRationalLiteral (11312888386879545843) 51200000000000000000),
          (exactRationalLiteral (319424507874091723) 38400000000000000000),
          (exactRationalLiteral (819679716995331961) 204800000000000000000),
          (exactRationalLiteral (46003273751752326389) 153600000000000000000),
          (exactRationalLiteral (48432571767231563213) 76800000000000000000),
          (exactRationalLiteral (46003273751752326389) 153600000000000000000),
          (exactRationalLiteral (819679716995331961) 204800000000000000000),
          (exactRationalLiteral (319424507874091723) 38400000000000000000),
          (exactRationalLiteral (11312888386879545843) 51200000000000000000),
          (exactRationalLiteral (6861946458062732953) 38400000000000000000),
          (exactRationalLiteral (149621405175363091) 3072000000000000000),
          (exactRationalLiteral (2871706859355708397) 153600000000000000000),
          (exactRationalLiteral (468403802745374867) 76800000000000000000),
          (exactRationalLiteral (228309964298888533) 122880000000000000000),
          (exactRationalLiteral (861118965832644639) 204800000000000000000),
          (exactRationalLiteral (37507122324108691) 3072000000000000000),
          (exactRationalLiteral (473963322713222011) 204800000000000000000),
          (exactRationalLiteral (3416876854275705563) 1228800000000000000000),
          (exactRationalLiteral (944973571455744739) 1228800000000000000000),
          (exactRationalLiteral (533058083984620627) 307200000000000000000),
          (exactRationalLiteral (43884313275518299) 25600000000000000000),
          (exactRationalLiteral (21679817166770183) 1280000000000000000),
          (exactRationalLiteral (6853434948235236791) 102400000000000000000),
          (exactRationalLiteral (22349761608133734819) 409600000000000000000),
          (exactRationalLiteral (1114856881803736301) 38400000000000000000),
          (exactRationalLiteral (3916956772828221659) 153600000000000000000),
          (exactRationalLiteral (2745191161656999) 5120000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 5),
      (28, 21)
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
            (exactRationalLiteral (74120161364738973) 327680000000000000000),
            (exactRationalLiteral (-24706720454912991) 10240000000000000000),
            (exactRationalLiteral (2745191161656999) 320000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (217174245627560262281) 9830400000000000000000),
            (exactRationalLiteral (-3941182399982044993) 102400000000000000000),
            (exactRationalLiteral (-54512535578476999) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-37649118371484700109) 2457600000000000000000),
            (exactRationalLiteral (3688334496699102909) 25600000000000000000),
            (exactRationalLiteral (-29769520976002157) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-195841531601400075943) 3276800000000000000000),
            (exactRationalLiteral (-3320655683217955287) 20480000000000000000),
            (exactRationalLiteral (459031241073563931) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (168697200357043511113) 2457600000000000000000),
            (exactRationalLiteral (254993191310764131) 5120000000000000000),
            (exactRationalLiteral (-133380813400375271) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1324742654119219991) 81920000000000000000),
            (exactRationalLiteral (204024853421227593) 12800000000000000000),
            (exactRationalLiteral (35260106771941383) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2074112410712031001) 1638400000000000000000),
            (exactRationalLiteral (-349691668040827059) 51200000000000000000),
            (exactRationalLiteral (-37086744117551397) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-16808106717617330983) 9830400000000000000000),
            (exactRationalLiteral (70791697862250031) 102400000000000000000),
            (exactRationalLiteral (17010897408538889) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (7556073405549686231) 9830400000000000000000),
            (exactRationalLiteral (-7038618898220671) 102400000000000000000),
            (exactRationalLiteral (-5920767074235673) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (27712718834733904991) 9830400000000000000000),
            (exactRationalLiteral (129386087619760473) 102400000000000000000),
            (exactRationalLiteral (3546264903341231) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (11649733536453768581) 4915200000000000000000),
            (exactRationalLiteral (91153161249194451) 51200000000000000000),
            (exactRationalLiteral (-16108217890723) 64000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2520880470451471071) 204800000000000000000),
            (exactRationalLiteral (-20444653293533263) 6400000000000000000),
            (exactRationalLiteral (-36552445809093) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-20770386186322908737) 4915200000000000000000),
            (exactRationalLiteral (-37530797950034551) 51200000000000000000),
            (exactRationalLiteral (-3058936956879377) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (9773301062127904493) 4915200000000000000000),
            (exactRationalLiteral (214208378915811979) 51200000000000000000),
            (exactRationalLiteral (118988602400473) 320000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-26494203634170362249) 4915200000000000000000),
            (exactRationalLiteral (382465727538408993) 51200000000000000000),
            (exactRationalLiteral (-1503122583718649) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-161611903374712503247) 9830400000000000000000),
            (exactRationalLiteral (2350090856849596247) 102400000000000000000),
            (exactRationalLiteral (-39256886152875679) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (231743421540300824929) 4915200000000000000000),
            (exactRationalLiteral (-261919832519085477) 10240000000000000000),
            (exactRationalLiteral (-133018161223983791) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (75311506840658411411) 491520000000000000000),
            (exactRationalLiteral (-5836952503678109143) 25600000000000000000),
            (exactRationalLiteral (339394582473910927) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-601726123283427905913) 3276800000000000000000),
            (exactRationalLiteral (34739493059792214643) 102400000000000000000),
            (exactRationalLiteral (-1837834344051929403) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-12218184861806338979) 2457600000000000000000),
            (exactRationalLiteral (-2873359978717915077) 25600000000000000000),
            (exactRationalLiteral (45821432044645961) 160000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (38181163074936050201) 9830400000000000000000),
            (exactRationalLiteral (-76933838237092253) 20480000000000000000),
            (exactRationalLiteral (-102774733554900919) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-2777149427182675577471) 9830400000000000000000),
            (exactRationalLiteral (17813473142488759143) 102400000000000000000),
            (exactRationalLiteral (-238883067668245007) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2929597844812515538343) 4915200000000000000000),
            (exactRationalLiteral (-18219046550243086031) 51200000000000000000),
            (exactRationalLiteral (43637965077561739) 320000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2777149427182675577471) 9830400000000000000000),
            (exactRationalLiteral (17813473142488759143) 102400000000000000000),
            (exactRationalLiteral (-238883067668245007) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (38181163074936050201) 9830400000000000000000),
            (exactRationalLiteral (-76933838237092253) 20480000000000000000),
            (exactRationalLiteral (-102774733554900919) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-12218184861806338979) 2457600000000000000000),
            (exactRationalLiteral (-2873359978717915077) 25600000000000000000),
            (exactRationalLiteral (45821432044645961) 160000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-601726123283427905913) 3276800000000000000000),
            (exactRationalLiteral (34739493059792214643) 102400000000000000000),
            (exactRationalLiteral (-1837834344051929403) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (75311506840658411411) 491520000000000000000),
            (exactRationalLiteral (-5836952503678109143) 25600000000000000000),
            (exactRationalLiteral (339394582473910927) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (231743421540300824929) 4915200000000000000000),
            (exactRationalLiteral (-261919832519085477) 10240000000000000000),
            (exactRationalLiteral (-133018161223983791) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-161611903374712503247) 9830400000000000000000),
            (exactRationalLiteral (2350090856849596247) 102400000000000000000),
            (exactRationalLiteral (-39256886152875679) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-26494203634170362249) 4915200000000000000000),
            (exactRationalLiteral (382465727538408993) 51200000000000000000),
            (exactRationalLiteral (-1503122583718649) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (9773301062127904493) 4915200000000000000000),
            (exactRationalLiteral (214208378915811979) 51200000000000000000),
            (exactRationalLiteral (118988602400473) 320000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20770386186322908737) 4915200000000000000000),
            (exactRationalLiteral (-37530797950034551) 51200000000000000000),
            (exactRationalLiteral (-3058936956879377) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2520880470451471071) 204800000000000000000),
            (exactRationalLiteral (-20444653293533263) 6400000000000000000),
            (exactRationalLiteral (-36552445809093) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (11649733536453768581) 4915200000000000000000),
            (exactRationalLiteral (91153161249194451) 51200000000000000000),
            (exactRationalLiteral (-16108217890723) 64000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (27712718834733904991) 9830400000000000000000),
            (exactRationalLiteral (129386087619760473) 102400000000000000000),
            (exactRationalLiteral (3546264903341231) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7556073405549686231) 9830400000000000000000),
            (exactRationalLiteral (-7038618898220671) 102400000000000000000),
            (exactRationalLiteral (-5920767074235673) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-16808106717617330983) 9830400000000000000000),
            (exactRationalLiteral (70791697862250031) 102400000000000000000),
            (exactRationalLiteral (17010897408538889) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2074112410712031001) 1638400000000000000000),
            (exactRationalLiteral (-349691668040827059) 51200000000000000000),
            (exactRationalLiteral (-37086744117551397) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1324742654119219991) 81920000000000000000),
            (exactRationalLiteral (204024853421227593) 12800000000000000000),
            (exactRationalLiteral (35260106771941383) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (168697200357043511113) 2457600000000000000000),
            (exactRationalLiteral (254993191310764131) 5120000000000000000),
            (exactRationalLiteral (-133380813400375271) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-195841531601400075943) 3276800000000000000000),
            (exactRationalLiteral (-3320655683217955287) 20480000000000000000),
            (exactRationalLiteral (459031241073563931) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-37649118371484700109) 2457600000000000000000),
            (exactRationalLiteral (3688334496699102909) 25600000000000000000),
            (exactRationalLiteral (-29769520976002157) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (217174245627560262281) 9830400000000000000000),
            (exactRationalLiteral (-3941182399982044993) 102400000000000000000),
            (exactRationalLiteral (-54512535578476999) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (74120161364738973) 327680000000000000000),
            (exactRationalLiteral (-24706720454912991) 10240000000000000000),
            (exactRationalLiteral (2745191161656999) 320000000000000000),
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
          (exactRationalLiteral (101673746728037) 327680000000000000),
          (exactRationalLiteral (28602023498402974477) 1228800000000000000000),
          (exactRationalLiteral (6099053499949448389) 307200000000000000000),
          (exactRationalLiteral (413997866905435831) 6400000000000000000),
          (exactRationalLiteral (336155619289138843) 4800000000000000000),
          (exactRationalLiteral (2547444459570549649) 153600000000000000000),
          (exactRationalLiteral (895285518986248631) 614400000000000000000),
          (exactRationalLiteral (424262265602191783) 245760000000000000000),
          (exactRationalLiteral (236520974403057059) 307200000000000000000),
          (exactRationalLiteral (18301888297319149) 6400000000000000000),
          (exactRationalLiteral (23285021670130079) 9600000000000000000),
          (exactRationalLiteral (29781553408445089) 2400000000000000000),
          (exactRationalLiteral (1632208657375283) 384000000000000000),
          (exactRationalLiteral (6782404433836121) 3200000000000000000),
          (exactRationalLiteral (1151922590843240223) 204800000000000000000),
          (exactRationalLiteral (4219467722487700591) 245760000000000000000),
          (exactRationalLiteral (5881325340119609297) 122880000000000000000),
          (exactRationalLiteral (49390038658888997411) 307200000000000000000),
          (exactRationalLiteral (239385179357741171783) 1228800000000000000000),
          (exactRationalLiteral (39401814944885737) 4800000000000000000),
          (exactRationalLiteral (4876669994303336573) 1228800000000000000000),
          (exactRationalLiteral (117971549967245354617) 409600000000000000000),
          (exactRationalLiteral (373114732224151240307) 614400000000000000000),
          (exactRationalLiteral (117971549967245354617) 409600000000000000000),
          (exactRationalLiteral (4876669994303336573) 1228800000000000000000),
          (exactRationalLiteral (39401814944885737) 4800000000000000000),
          (exactRationalLiteral (239385179357741171783) 1228800000000000000000),
          (exactRationalLiteral (49390038658888997411) 307200000000000000000),
          (exactRationalLiteral (5881325340119609297) 122880000000000000000),
          (exactRationalLiteral (4219467722487700591) 245760000000000000000),
          (exactRationalLiteral (1151922590843240223) 204800000000000000000),
          (exactRationalLiteral (6782404433836121) 3200000000000000000),
          (exactRationalLiteral (1632208657375283) 384000000000000000),
          (exactRationalLiteral (29781553408445089) 2400000000000000000),
          (exactRationalLiteral (23285021670130079) 9600000000000000000),
          (exactRationalLiteral (18301888297319149) 6400000000000000000),
          (exactRationalLiteral (236520974403057059) 307200000000000000000),
          (exactRationalLiteral (424262265602191783) 245760000000000000000),
          (exactRationalLiteral (895285518986248631) 614400000000000000000),
          (exactRationalLiteral (2547444459570549649) 153600000000000000000),
          (exactRationalLiteral (336155619289138843) 4800000000000000000),
          (exactRationalLiteral (413997866905435831) 6400000000000000000),
          (exactRationalLiteral (6099053499949448389) 307200000000000000000),
          (exactRationalLiteral (28602023498402974477) 1228800000000000000000),
          (exactRationalLiteral (101673746728037) 327680000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 4),
      (28, 20)
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
            (exactRationalLiteral (34874095127716691) 327680000000000000000),
            (exactRationalLiteral (-14946040769021439) 10240000000000000000),
            (exactRationalLiteral (2135148681288777) 320000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (193017538669103631911) 9830400000000000000000),
            (exactRationalLiteral (-4086963608107271201) 102400000000000000000),
            (exactRationalLiteral (-3675613696827221) 640000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-15964365042317534099) 2457600000000000000000),
            (exactRationalLiteral (3525246713137381501) 25600000000000000000),
            (exactRationalLiteral (-51774370804858547) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-227060996102620229289) 3276800000000000000000),
            (exactRationalLiteral (-14540702401797805011) 102400000000000000000),
            (exactRationalLiteral (572256766072421781) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (58221398883947951533) 819200000000000000000),
            (exactRationalLiteral (28013114443731239) 1024000000000000000),
            (exactRationalLiteral (-153938234329894569) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-3641379282274345627) 245760000000000000000),
            (exactRationalLiteral (353551779821947913) 12800000000000000000),
            (exactRationalLiteral (39503356428418777) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (3662089110607961413) 4915200000000000000000),
            (exactRationalLiteral (-506567236447308883) 51200000000000000000),
            (exactRationalLiteral (-8270208017137903) 320000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-16170893720667708841) 9830400000000000000000),
            (exactRationalLiteral (143001307933233231) 102400000000000000000),
            (exactRationalLiteral (19093907626952711) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (7439899602275000633) 9830400000000000000000),
            (exactRationalLiteral (-32168129692430111) 102400000000000000000),
            (exactRationalLiteral (-6643988322869047) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (28533066798324584689) 9830400000000000000000),
            (exactRationalLiteral (144309276749136441) 102400000000000000000),
            (exactRationalLiteral (3915329661346753) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4063796522852713433) 1638400000000000000000),
            (exactRationalLiteral (89327104448333107) 51200000000000000000),
            (exactRationalLiteral (-510322953162597) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7685689112381341931) 614400000000000000000),
            (exactRationalLiteral (-20561439034779647) 6400000000000000000),
            (exactRationalLiteral (-21840424814099) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-7011067201461814533) 1638400000000000000000),
            (exactRationalLiteral (-2009129568697583) 2048000000000000000),
            (exactRationalLiteral (-657956735364627) 320000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2213237622290855879) 983040000000000000000),
            (exactRationalLiteral (216836880807558763) 51200000000000000000),
            (exactRationalLiteral (719307933871027) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8072396924778790221) 1638400000000000000000),
            (exactRationalLiteral (75316244001523021) 10240000000000000000),
            (exactRationalLiteral (-287826236335659) 320000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-147992342501144596993) 9830400000000000000000),
            (exactRationalLiteral (2188112495390511991) 102400000000000000000),
            (exactRationalLiteral (-41732294576666449) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (8898032645883469031) 196608000000000000000),
            (exactRationalLiteral (-70442721958729089) 2048000000000000000),
            (exactRationalLiteral (-92716281962416129) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (345338683695999437137) 2457600000000000000000),
            (exactRationalLiteral (-4614309411237913527) 25600000000000000000),
            (exactRationalLiteral (271926963746186881) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1617426761219247787621) 9830400000000000000000),
            (exactRationalLiteral (28072486884037394579) 102400000000000000000),
            (exactRationalLiteral (-1495668743825480629) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-26891346287363892173) 2457600000000000000000),
            (exactRationalLiteral (-2048075075789406053) 25600000000000000000),
            (exactRationalLiteral (183535291241024707) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (34747743072372780823) 9830400000000000000000),
            (exactRationalLiteral (-741822151800910321) 102400000000000000000),
            (exactRationalLiteral (-75801746752823609) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-891016519311275531867) 3276800000000000000000),
            (exactRationalLiteral (16900754474783462663) 102400000000000000000),
            (exactRationalLiteral (-217476266184403233) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2822835412585297127017) 4915200000000000000000),
            (exactRationalLiteral (-17379502663898650991) 51200000000000000000),
            (exactRationalLiteral (8063284711376353) 64000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-891016519311275531867) 3276800000000000000000),
            (exactRationalLiteral (16900754474783462663) 102400000000000000000),
            (exactRationalLiteral (-217476266184403233) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (34747743072372780823) 9830400000000000000000),
            (exactRationalLiteral (-741822151800910321) 102400000000000000000),
            (exactRationalLiteral (-75801746752823609) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-26891346287363892173) 2457600000000000000000),
            (exactRationalLiteral (-2048075075789406053) 25600000000000000000),
            (exactRationalLiteral (183535291241024707) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1617426761219247787621) 9830400000000000000000),
            (exactRationalLiteral (28072486884037394579) 102400000000000000000),
            (exactRationalLiteral (-1495668743825480629) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (345338683695999437137) 2457600000000000000000),
            (exactRationalLiteral (-4614309411237913527) 25600000000000000000),
            (exactRationalLiteral (271926963746186881) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (8898032645883469031) 196608000000000000000),
            (exactRationalLiteral (-70442721958729089) 2048000000000000000),
            (exactRationalLiteral (-92716281962416129) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-147992342501144596993) 9830400000000000000000),
            (exactRationalLiteral (2188112495390511991) 102400000000000000000),
            (exactRationalLiteral (-41732294576666449) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-8072396924778790221) 1638400000000000000000),
            (exactRationalLiteral (75316244001523021) 10240000000000000000),
            (exactRationalLiteral (-287826236335659) 320000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2213237622290855879) 983040000000000000000),
            (exactRationalLiteral (216836880807558763) 51200000000000000000),
            (exactRationalLiteral (719307933871027) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7011067201461814533) 1638400000000000000000),
            (exactRationalLiteral (-2009129568697583) 2048000000000000000),
            (exactRationalLiteral (-657956735364627) 320000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7685689112381341931) 614400000000000000000),
            (exactRationalLiteral (-20561439034779647) 6400000000000000000),
            (exactRationalLiteral (-21840424814099) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (4063796522852713433) 1638400000000000000000),
            (exactRationalLiteral (89327104448333107) 51200000000000000000),
            (exactRationalLiteral (-510322953162597) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (28533066798324584689) 9830400000000000000000),
            (exactRationalLiteral (144309276749136441) 102400000000000000000),
            (exactRationalLiteral (3915329661346753) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7439899602275000633) 9830400000000000000000),
            (exactRationalLiteral (-32168129692430111) 102400000000000000000),
            (exactRationalLiteral (-6643988322869047) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-16170893720667708841) 9830400000000000000000),
            (exactRationalLiteral (143001307933233231) 102400000000000000000),
            (exactRationalLiteral (19093907626952711) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (3662089110607961413) 4915200000000000000000),
            (exactRationalLiteral (-506567236447308883) 51200000000000000000),
            (exactRationalLiteral (-8270208017137903) 320000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3641379282274345627) 245760000000000000000),
            (exactRationalLiteral (353551779821947913) 12800000000000000000),
            (exactRationalLiteral (39503356428418777) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (58221398883947951533) 819200000000000000000),
            (exactRationalLiteral (28013114443731239) 1024000000000000000),
            (exactRationalLiteral (-153938234329894569) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-227060996102620229289) 3276800000000000000000),
            (exactRationalLiteral (-14540702401797805011) 102400000000000000000),
            (exactRationalLiteral (572256766072421781) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-15964365042317534099) 2457600000000000000000),
            (exactRationalLiteral (3525246713137381501) 25600000000000000000),
            (exactRationalLiteral (-51774370804858547) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (193017538669103631911) 9830400000000000000000),
            (exactRationalLiteral (-4086963608107271201) 102400000000000000000),
            (exactRationalLiteral (-3675613696827221) 640000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (34874095127716691) 327680000000000000000),
            (exactRationalLiteral (-14946040769021439) 10240000000000000000),
            (exactRationalLiteral (2135148681288777) 320000000000000000),
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
          (exactRationalLiteral (101673746728037) 640000000000000000),
          (exactRationalLiteral (400791461043800521) 19200000000000000000),
          (exactRationalLiteral (3257376204739969) 300000000000000000),
          (exactRationalLiteral (30126321352189058693) 409600000000000000000),
          (exactRationalLiteral (22036635852708656771) 307200000000000000000),
          (exactRationalLiteral (935115395819363) 60000000000000000),
          (exactRationalLiteral (9882558296243923) 9600000000000000000),
          (exactRationalLiteral (32311830911515151) 19200000000000000000),
          (exactRationalLiteral (14681315697281251) 19200000000000000000),
          (exactRationalLiteral (3622240643741879629) 1228800000000000000000),
          (exactRationalLiteral (1557223263036338071) 614400000000000000000),
          (exactRationalLiteral (322809649781234403) 25600000000000000000),
          (exactRationalLiteral (2649233887053525451) 614400000000000000000),
          (exactRationalLiteral (1464864857517437887) 614400000000000000000),
          (exactRationalLiteral (9902845243595809) 1920000000000000000),
          (exactRationalLiteral (302110623372723119) 19200000000000000000),
          (exactRationalLiteral (148070130539370687) 3200000000000000000),
          (exactRationalLiteral (703185794199835157) 4800000000000000000),
          (exactRationalLiteral (3332621700982323511) 19200000000000000000),
          (exactRationalLiteral (812693789387503469) 61440000000000000000),
          (exactRationalLiteral (23914269397210939) 6400000000000000000),
          (exactRationalLiteral (5321122956166937723) 19200000000000000000),
          (exactRationalLiteral (74885077364170521) 128000000000000000),
          (exactRationalLiteral (5321122956166937723) 19200000000000000000),
          (exactRationalLiteral (23914269397210939) 6400000000000000000),
          (exactRationalLiteral (812693789387503469) 61440000000000000000),
          (exactRationalLiteral (3332621700982323511) 19200000000000000000),
          (exactRationalLiteral (703185794199835157) 4800000000000000000),
          (exactRationalLiteral (148070130539370687) 3200000000000000000),
          (exactRationalLiteral (302110623372723119) 19200000000000000000),
          (exactRationalLiteral (9902845243595809) 1920000000000000000),
          (exactRationalLiteral (1464864857517437887) 614400000000000000000),
          (exactRationalLiteral (2649233887053525451) 614400000000000000000),
          (exactRationalLiteral (322809649781234403) 25600000000000000000),
          (exactRationalLiteral (1557223263036338071) 614400000000000000000),
          (exactRationalLiteral (3622240643741879629) 1228800000000000000000),
          (exactRationalLiteral (14681315697281251) 19200000000000000000),
          (exactRationalLiteral (32311830911515151) 19200000000000000000),
          (exactRationalLiteral (9882558296243923) 9600000000000000000),
          (exactRationalLiteral (935115395819363) 60000000000000000),
          (exactRationalLiteral (22036635852708656771) 307200000000000000000),
          (exactRationalLiteral (30126321352189058693) 409600000000000000000),
          (exactRationalLiteral (3257376204739969) 300000000000000000),
          (exactRationalLiteral (400791461043800521) 19200000000000000000),
          (exactRationalLiteral (101673746728037) 640000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 3),
      (28, 19)
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
            (exactRationalLiteral (101673746728037) 2621440000000000000),
            (exactRationalLiteral (-305021240184111) 409600000000000000),
            (exactRationalLiteral (305021240184111) 64000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (168419758067027735021) 9830400000000000000000),
            (exactRationalLiteral (-4088206947855133833) 102400000000000000000),
            (exactRationalLiteral (17756398610204789) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (4477803387533026783) 2457600000000000000000),
            (exactRationalLiteral (3274139530260234533) 25600000000000000000),
            (exactRationalLiteral (-73779220633714937) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-253702406475261008387) 3276800000000000000000),
            (exactRationalLiteral (-12025224287510402187) 102400000000000000000),
            (exactRationalLiteral (685482291071279631) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (176936675322726728429) 2457600000000000000000),
            (exactRationalLiteral (43460081914664103) 25600000000000000000),
            (exactRationalLiteral (-174495655259413867) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-15594572456673105757) 1228800000000000000000),
            (exactRationalLiteral (520051704848577809) 12800000000000000000),
            (exactRationalLiteral (43746606084896171) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (109416027023281463) 4915200000000000000000),
            (exactRationalLiteral (-680499988726343179) 51200000000000000000),
            (exactRationalLiteral (-45615336053827633) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3015085388134244327) 1966080000000000000000),
            (exactRationalLiteral (223542958877871719) 102400000000000000000),
            (exactRationalLiteral (21176917845366533) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (7164270079251457907) 9830400000000000000000),
            (exactRationalLiteral (-60190525481173047) 102400000000000000000),
            (exactRationalLiteral (-7367209571502421) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (9815794224595862153) 3276800000000000000000),
            (exactRationalLiteral (160708724910534497) 102400000000000000000),
            (exactRationalLiteral (171375776774091) 128000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (12720797849786609689) 4915200000000000000000),
            (exactRationalLiteral (3482823104955747) 2048000000000000000),
            (exactRationalLiteral (-617940459057119) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-312370439344152361) 24576000000000000000),
            (exactRationalLiteral (-4123875338409211) 1280000000000000000),
            (exactRationalLiteral (-1425680763821) 40000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-21374971830691733701) 4915200000000000000000),
            (exactRationalLiteral (-63849067364619631) 51200000000000000000),
            (exactRationalLiteral (-3520630396766893) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (825089236746237263) 327680000000000000000),
            (exactRationalLiteral (43992568477356039) 10240000000000000000),
            (exactRationalLiteral (843672855739689) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-21974717062862658157) 4915200000000000000000),
            (exactRationalLiteral (370952678084982633) 51200000000000000000),
            (exactRationalLiteral (-1375139779637941) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-27074871339483337103) 1966080000000000000000),
            (exactRationalLiteral (403246500047252931) 20480000000000000000),
            (exactRationalLiteral (-44207703000457219) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (2812440266490328527) 65536000000000000000),
            (exactRationalLiteral (-2051329418294756417) 51200000000000000000),
            (exactRationalLiteral (-52414402700848467) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (320646080318615302363) 2457600000000000000000),
            (exactRationalLiteral (-732307358741722819) 5120000000000000000),
            (exactRationalLiteral (40891869003692567) 160000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1465571202440023392599) 9830400000000000000000),
            (exactRationalLiteral (22774143109188369611) 102400000000000000000),
            (exactRationalLiteral (-230700628719806371) 640000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-37159660723136852399) 2457600000000000000000),
            (exactRationalLiteral (-1405077648789717421) 25600000000000000000),
            (exactRationalLiteral (137963422258819609) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (9831693715913914943) 3276800000000000000000),
            (exactRationalLiteral (-991083165208050137) 102400000000000000000),
            (exactRationalLiteral (-48828759950746299) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-2574169119073403291323) 9830400000000000000000),
            (exactRationalLiteral (16073663013013533279) 102400000000000000000),
            (exactRationalLiteral (-196069464700561459) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (906970317061634842497) 1638400000000000000000),
            (exactRationalLiteral (-16606389607967815431) 51200000000000000000),
            (exactRationalLiteral (36994882036201791) 320000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2574169119073403291323) 9830400000000000000000),
            (exactRationalLiteral (16073663013013533279) 102400000000000000000),
            (exactRationalLiteral (-196069464700561459) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9831693715913914943) 3276800000000000000000),
            (exactRationalLiteral (-991083165208050137) 102400000000000000000),
            (exactRationalLiteral (-48828759950746299) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-37159660723136852399) 2457600000000000000000),
            (exactRationalLiteral (-1405077648789717421) 25600000000000000000),
            (exactRationalLiteral (137963422258819609) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1465571202440023392599) 9830400000000000000000),
            (exactRationalLiteral (22774143109188369611) 102400000000000000000),
            (exactRationalLiteral (-230700628719806371) 640000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (320646080318615302363) 2457600000000000000000),
            (exactRationalLiteral (-732307358741722819) 5120000000000000000),
            (exactRationalLiteral (40891869003692567) 160000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (2812440266490328527) 65536000000000000000),
            (exactRationalLiteral (-2051329418294756417) 51200000000000000000),
            (exactRationalLiteral (-52414402700848467) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-27074871339483337103) 1966080000000000000000),
            (exactRationalLiteral (403246500047252931) 20480000000000000000),
            (exactRationalLiteral (-44207703000457219) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-21974717062862658157) 4915200000000000000000),
            (exactRationalLiteral (370952678084982633) 51200000000000000000),
            (exactRationalLiteral (-1375139779637941) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (825089236746237263) 327680000000000000000),
            (exactRationalLiteral (43992568477356039) 10240000000000000000),
            (exactRationalLiteral (843672855739689) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-21374971830691733701) 4915200000000000000000),
            (exactRationalLiteral (-63849067364619631) 51200000000000000000),
            (exactRationalLiteral (-3520630396766893) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-312370439344152361) 24576000000000000000),
            (exactRationalLiteral (-4123875338409211) 1280000000000000000),
            (exactRationalLiteral (-1425680763821) 40000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (12720797849786609689) 4915200000000000000000),
            (exactRationalLiteral (3482823104955747) 2048000000000000000),
            (exactRationalLiteral (-617940459057119) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (9815794224595862153) 3276800000000000000000),
            (exactRationalLiteral (160708724910534497) 102400000000000000000),
            (exactRationalLiteral (171375776774091) 128000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7164270079251457907) 9830400000000000000000),
            (exactRationalLiteral (-60190525481173047) 102400000000000000000),
            (exactRationalLiteral (-7367209571502421) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-3015085388134244327) 1966080000000000000000),
            (exactRationalLiteral (223542958877871719) 102400000000000000000),
            (exactRationalLiteral (21176917845366533) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (109416027023281463) 4915200000000000000000),
            (exactRationalLiteral (-680499988726343179) 51200000000000000000),
            (exactRationalLiteral (-45615336053827633) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-15594572456673105757) 1228800000000000000000),
            (exactRationalLiteral (520051704848577809) 12800000000000000000),
            (exactRationalLiteral (43746606084896171) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (176936675322726728429) 2457600000000000000000),
            (exactRationalLiteral (43460081914664103) 25600000000000000000),
            (exactRationalLiteral (-174495655259413867) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-253702406475261008387) 3276800000000000000000),
            (exactRationalLiteral (-12025224287510402187) 102400000000000000000),
            (exactRationalLiteral (685482291071279631) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (4477803387533026783) 2457600000000000000000),
            (exactRationalLiteral (3274139530260234533) 25600000000000000000),
            (exactRationalLiteral (-73779220633714937) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (168419758067027735021) 9830400000000000000000),
            (exactRationalLiteral (-4088206947855133833) 102400000000000000000),
            (exactRationalLiteral (17756398610204789) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (101673746728037) 2621440000000000000),
            (exactRationalLiteral (-305021240184111) 409600000000000000),
            (exactRationalLiteral (305021240184111) 64000000000000000),
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
          (exactRationalLiteral (2745191161656999) 40960000000000000000),
          (exactRationalLiteral (4517989521821914511) 245760000000000000000),
          (exactRationalLiteral (219810654554658709) 38400000000000000000),
          (exactRationalLiteral (4140988711732296687) 51200000000000000000),
          (exactRationalLiteral (5536403430323923939) 76800000000000000000),
          (exactRationalLiteral (709400390741349557) 51200000000000000000),
          (exactRationalLiteral (32360345239082813) 76800000000000000000),
          (exactRationalLiteral (1960445821109743013) 1228800000000000000000),
          (exactRationalLiteral (915387704700598309) 1228800000000000000000),
          (exactRationalLiteral (467852290064941399) 153600000000000000000),
          (exactRationalLiteral (67604697669417563) 25600000000000000000),
          (exactRationalLiteral (30746613839378543) 2400000000000000000),
          (exactRationalLiteral (112381230975707631) 25600000000000000000),
          (exactRationalLiteral (203731566865344577) 76800000000000000000),
          (exactRationalLiteral (2886466564019692507) 614400000000000000000),
          (exactRationalLiteral (17694304950364369469) 1228800000000000000000),
          (exactRationalLiteral (27113701761740697443) 614400000000000000000),
          (exactRationalLiteral (41534725318020049397) 307200000000000000000),
          (exactRationalLiteral (64063550999937450891) 409600000000000000000),
          (exactRationalLiteral (640371708394072631) 38400000000000000000),
          (exactRationalLiteral (4038544733764077211) 1228800000000000000000),
          (exactRationalLiteral (327873627488410937053) 1228800000000000000000),
          (exactRationalLiteral (346411668386644087573) 614400000000000000000),
          (exactRationalLiteral (327873627488410937053) 1228800000000000000000),
          (exactRationalLiteral (4038544733764077211) 1228800000000000000000),
          (exactRationalLiteral (640371708394072631) 38400000000000000000),
          (exactRationalLiteral (64063550999937450891) 409600000000000000000),
          (exactRationalLiteral (41534725318020049397) 307200000000000000000),
          (exactRationalLiteral (27113701761740697443) 614400000000000000000),
          (exactRationalLiteral (17694304950364369469) 1228800000000000000000),
          (exactRationalLiteral (2886466564019692507) 614400000000000000000),
          (exactRationalLiteral (203731566865344577) 76800000000000000000),
          (exactRationalLiteral (112381230975707631) 25600000000000000000),
          (exactRationalLiteral (30746613839378543) 2400000000000000000),
          (exactRationalLiteral (67604697669417563) 25600000000000000000),
          (exactRationalLiteral (467852290064941399) 153600000000000000000),
          (exactRationalLiteral (915387704700598309) 1228800000000000000000),
          (exactRationalLiteral (1960445821109743013) 1228800000000000000000),
          (exactRationalLiteral (32360345239082813) 76800000000000000000),
          (exactRationalLiteral (709400390741349557) 51200000000000000000),
          (exactRationalLiteral (5536403430323923939) 76800000000000000000),
          (exactRationalLiteral (4140988711732296687) 51200000000000000000),
          (exactRationalLiteral (219810654554658709) 38400000000000000000),
          (exactRationalLiteral (4517989521821914511) 245760000000000000000),
          (exactRationalLiteral (2745191161656999) 40960000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 2),
      (28, 18)
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
            (exactRationalLiteral (2745191161656999) 327680000000000000000),
            (exactRationalLiteral (-2745191161656999) 10240000000000000000),
            (exactRationalLiteral (915063720552333) 320000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (144248131031596753067) 9830400000000000000000),
            (exactRationalLiteral (-3944912419225632889) 102400000000000000000),
            (exactRationalLiteral (53890865704545683) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (23149270522174429177) 2457600000000000000000),
            (exactRationalLiteral (587002589613532401) 5120000000000000000),
            (exactRationalLiteral (-95784070462571327) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-274859958519331550437) 3276800000000000000000),
            (exactRationalLiteral (-9056844073227567963) 102400000000000000000),
            (exactRationalLiteral (798707816070137481) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (175021258267383669451) 2457600000000000000000),
            (exactRationalLiteral (-695637380982029961) 25600000000000000000),
            (exactRationalLiteral (-39010615237786633) 160000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-159097732745826337) 16384000000000000000),
            (exactRationalLiteral (703524628501117281) 12800000000000000000),
            (exactRationalLiteral (9597971148274713) 80000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-1512675040617753893) 1638400000000000000000),
            (exactRationalLiteral (-871489924877929947) 51200000000000000000),
            (exactRationalLiteral (-49879632021965751) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-13471714132385937637) 9830400000000000000000),
            (exactRationalLiteral (62483330139233099) 20480000000000000000),
            (exactRationalLiteral (4651985612756071) 640000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (6711827526511857077) 9830400000000000000000),
            (exactRationalLiteral (-91105806264449479) 102400000000000000000),
            (exactRationalLiteral (-1618086164027159) 640000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (30464524015315042829) 9830400000000000000000),
            (exactRationalLiteral (178584432103954641) 102400000000000000000),
            (exactRationalLiteral (4653459177357797) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (13235375559997708223) 4915200000000000000000),
            (exactRationalLiteral (16876716155175231) 10240000000000000000),
            (exactRationalLiteral (-725557964951641) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2644334645505978213) 204800000000000000000),
            (exactRationalLiteral (-20618466265332487) 6400000000000000000),
            (exactRationalLiteral (7583617175889) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-4360247437304085847) 983040000000000000000),
            (exactRationalLiteral (-78393282391574719) 51200000000000000000),
            (exactRationalLiteral (-3751477116710651) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (13706737139470591031) 4915200000000000000000),
            (exactRationalLiteral (8943450546139051) 2048000000000000000),
            (exactRationalLiteral (968037777608351) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3953049341220051247) 983040000000000000000),
            (exactRationalLiteral (365580101770511577) 51200000000000000000),
            (exactRationalLiteral (-1311148377597587) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-123817355765699747293) 9830400000000000000000),
            (exactRationalLiteral (1834450871386854239) 102400000000000000000),
            (exactRationalLiteral (-46683111424247989) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (198157278161642190067) 4915200000000000000000),
            (exactRationalLiteral (-2180383270575014961) 51200000000000000000),
            (exactRationalLiteral (-2422504687856161) 320000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (300860501221674275629) 2457600000000000000000),
            (exactRationalLiteral (-2978634651090210847) 25600000000000000000),
            (exactRationalLiteral (136991726290738789) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-447133239702391920699) 3276800000000000000000),
            (exactRationalLiteral (18844461735245139739) 102400000000000000000),
            (exactRationalLiteral (-811337543372583081) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-44116853024698142009) 2457600000000000000000),
            (exactRationalLiteral (-944367697718849181) 25600000000000000000),
            (exactRationalLiteral (92391553276614511) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (23070528984292797659) 9830400000000000000000),
            (exactRationalLiteral (-1132452231406880713) 102400000000000000000),
            (exactRationalLiteral (-21855773148668989) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-2479994347365793462061) 9830400000000000000000),
            (exactRationalLiteral (15332198757178970991) 102400000000000000000),
            (exactRationalLiteral (-34932532643343937) 640000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (524685175125771228577) 983040000000000000000),
            (exactRationalLiteral (-15899707382450579351) 51200000000000000000),
            (exactRationalLiteral (33673340515521817) 320000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-2479994347365793462061) 9830400000000000000000),
            (exactRationalLiteral (15332198757178970991) 102400000000000000000),
            (exactRationalLiteral (-34932532643343937) 640000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (23070528984292797659) 9830400000000000000000),
            (exactRationalLiteral (-1132452231406880713) 102400000000000000000),
            (exactRationalLiteral (-21855773148668989) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-44116853024698142009) 2457600000000000000000),
            (exactRationalLiteral (-944367697718849181) 25600000000000000000),
            (exactRationalLiteral (92391553276614511) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-447133239702391920699) 3276800000000000000000),
            (exactRationalLiteral (18844461735245139739) 102400000000000000000),
            (exactRationalLiteral (-811337543372583081) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (300860501221674275629) 2457600000000000000000),
            (exactRationalLiteral (-2978634651090210847) 25600000000000000000),
            (exactRationalLiteral (136991726290738789) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (198157278161642190067) 4915200000000000000000),
            (exactRationalLiteral (-2180383270575014961) 51200000000000000000),
            (exactRationalLiteral (-2422504687856161) 320000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-123817355765699747293) 9830400000000000000000),
            (exactRationalLiteral (1834450871386854239) 102400000000000000000),
            (exactRationalLiteral (-46683111424247989) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-3953049341220051247) 983040000000000000000),
            (exactRationalLiteral (365580101770511577) 51200000000000000000),
            (exactRationalLiteral (-1311148377597587) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (13706737139470591031) 4915200000000000000000),
            (exactRationalLiteral (8943450546139051) 2048000000000000000),
            (exactRationalLiteral (968037777608351) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4360247437304085847) 983040000000000000000),
            (exactRationalLiteral (-78393282391574719) 51200000000000000000),
            (exactRationalLiteral (-3751477116710651) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2644334645505978213) 204800000000000000000),
            (exactRationalLiteral (-20618466265332487) 6400000000000000000),
            (exactRationalLiteral (7583617175889) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (13235375559997708223) 4915200000000000000000),
            (exactRationalLiteral (16876716155175231) 10240000000000000000),
            (exactRationalLiteral (-725557964951641) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (30464524015315042829) 9830400000000000000000),
            (exactRationalLiteral (178584432103954641) 102400000000000000000),
            (exactRationalLiteral (4653459177357797) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6711827526511857077) 9830400000000000000000),
            (exactRationalLiteral (-91105806264449479) 102400000000000000000),
            (exactRationalLiteral (-1618086164027159) 640000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-13471714132385937637) 9830400000000000000000),
            (exactRationalLiteral (62483330139233099) 20480000000000000000),
            (exactRationalLiteral (4651985612756071) 640000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1512675040617753893) 1638400000000000000000),
            (exactRationalLiteral (-871489924877929947) 51200000000000000000),
            (exactRationalLiteral (-49879632021965751) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-159097732745826337) 16384000000000000000),
            (exactRationalLiteral (703524628501117281) 12800000000000000000),
            (exactRationalLiteral (9597971148274713) 80000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (175021258267383669451) 2457600000000000000000),
            (exactRationalLiteral (-695637380982029961) 25600000000000000000),
            (exactRationalLiteral (-39010615237786633) 160000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-274859958519331550437) 3276800000000000000000),
            (exactRationalLiteral (-9056844073227567963) 102400000000000000000),
            (exactRationalLiteral (798707816070137481) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (23149270522174429177) 2457600000000000000000),
            (exactRationalLiteral (587002589613532401) 5120000000000000000),
            (exactRationalLiteral (-95784070462571327) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (144248131031596753067) 9830400000000000000000),
            (exactRationalLiteral (-3944912419225632889) 102400000000000000000),
            (exactRationalLiteral (53890865704545683) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2745191161656999) 327680000000000000000),
            (exactRationalLiteral (-2745191161656999) 10240000000000000000),
            (exactRationalLiteral (915063720552333) 320000000000000000),
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
          (exactRationalLiteral (101673746728037) 5120000000000000000),
          (exactRationalLiteral (2441038650825626849) 153600000000000000000),
          (exactRationalLiteral (3956994341259409127) 307200000000000000000),
          (exactRationalLiteral (35387402981956979743) 409600000000000000000),
          (exactRationalLiteral (919444218188686039) 12800000000000000000),
          (exactRationalLiteral (43440799684513891) 3840000000000000000),
          (exactRationalLiteral (913033242567127229) 614400000000000000000),
          (exactRationalLiteral (224066028209254687) 153600000000000000000),
          (exactRationalLiteral (108769300991704919) 153600000000000000000),
          (exactRationalLiteral (1292267592564082621) 409600000000000000000),
          (exactRationalLiteral (1685786977459691813) 614400000000000000000),
          (exactRationalLiteral (999353653556488367) 76800000000000000000),
          (exactRationalLiteral (2755973361050657153) 614400000000000000000),
          (exactRationalLiteral (119837185218539827) 40960000000000000000),
          (exactRationalLiteral (108676835688779187) 25600000000000000000),
          (exactRationalLiteral (2022805000155018103) 153600000000000000000),
          (exactRationalLiteral (3197530304115915761) 76800000000000000000),
          (exactRationalLiteral (969503481759940583) 7680000000000000000),
          (exactRationalLiteral (21883409370986596171) 153600000000000000000),
          (exactRationalLiteral (5836945924064493571) 307200000000000000000),
          (exactRationalLiteral (412325497901037409) 153600000000000000000),
          (exactRationalLiteral (13158987682436054453) 51200000000000000000),
          (exactRationalLiteral (41744350027152225127) 76800000000000000000),
          (exactRationalLiteral (13158987682436054453) 51200000000000000000),
          (exactRationalLiteral (412325497901037409) 153600000000000000000),
          (exactRationalLiteral (5836945924064493571) 307200000000000000000),
          (exactRationalLiteral (21883409370986596171) 153600000000000000000),
          (exactRationalLiteral (969503481759940583) 7680000000000000000),
          (exactRationalLiteral (3197530304115915761) 76800000000000000000),
          (exactRationalLiteral (2022805000155018103) 153600000000000000000),
          (exactRationalLiteral (108676835688779187) 25600000000000000000),
          (exactRationalLiteral (119837185218539827) 40960000000000000000),
          (exactRationalLiteral (2755973361050657153) 614400000000000000000),
          (exactRationalLiteral (999353653556488367) 76800000000000000000),
          (exactRationalLiteral (1685786977459691813) 614400000000000000000),
          (exactRationalLiteral (1292267592564082621) 409600000000000000000),
          (exactRationalLiteral (108769300991704919) 153600000000000000000),
          (exactRationalLiteral (224066028209254687) 153600000000000000000),
          (exactRationalLiteral (913033242567127229) 614400000000000000000),
          (exactRationalLiteral (43440799684513891) 3840000000000000000),
          (exactRationalLiteral (919444218188686039) 12800000000000000000),
          (exactRationalLiteral (35387402981956979743) 409600000000000000000),
          (exactRationalLiteral (3956994341259409127) 307200000000000000000),
          (exactRationalLiteral (2441038650825626849) 153600000000000000000),
          (exactRationalLiteral (101673746728037) 5120000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 1),
      (28, 17)
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
            (exactRationalLiteral (101673746728037) 327680000000000000000),
            (exactRationalLiteral (-305021240184111) 10240000000000000000),
            (exactRationalLiteral (305021240184111) 320000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (24273976954614973501) 1966080000000000000000),
            (exactRationalLiteral (-3657080022218768369) 102400000000000000000),
            (exactRationalLiteral (90025332798886577) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (39521919965714119723) 2457600000000000000000),
            (exactRationalLiteral (2507866966559663917) 25600000000000000000),
            (exactRationalLiteral (-117788920291427717) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-289627848034840992639) 3276800000000000000000),
            (exactRationalLiteral (-5635561758949302339) 102400000000000000000),
            (exactRationalLiteral (911933341068995331) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (56141522461168738171) 819200000000000000000),
            (exactRationalLiteral (-1516964527596801217) 25600000000000000000),
            (exactRationalLiteral (-215610497118452463) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-7118330917407879233) 1228800000000000000000),
            (exactRationalLiteral (903970550779566329) 12800000000000000000),
            (exactRationalLiteral (52233105397850959) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-2076515487851396569) 983040000000000000000),
            (exactRationalLiteral (-1079537044902069187) 51200000000000000000),
            (exactRationalLiteral (-54143927990103869) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-11309763050569925119) 9830400000000000000000),
            (exactRationalLiteral (409622383388114559) 102400000000000000000),
            (exactRationalLiteral (25342938282194177) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (6065214634088997167) 9830400000000000000000),
            (exactRationalLiteral (-124913972042259407) 102400000000000000000),
            (exactRationalLiteral (-8813652068769169) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (31593348377099086327) 9830400000000000000000),
            (exactRationalLiteral (197936398329396873) 102400000000000000000),
            (exactRationalLiteral (5022523935363319) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4577513293016655791) 1638400000000000000000),
            (exactRationalLiteral (81266113904280547) 51200000000000000000),
            (exactRationalLiteral (-833175470846163) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8056564882619838917) 614400000000000000000),
            (exactRationalLiteral (-20558707754638943) 6400000000000000000),
            (exactRationalLiteral (22295638170883) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-7439179331050060131) 1638400000000000000000),
            (exactRationalLiteral (-93860884298304839) 51200000000000000000),
            (exactRationalLiteral (-3982323836654409) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (15060368634410223541) 4915200000000000000000),
            (exactRationalLiteral (227707144607647003) 51200000000000000000),
            (exactRationalLiteral (1092402699477013) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5862414636800065467) 1638400000000000000000),
            (exactRationalLiteral (360463491064201937) 51200000000000000000),
            (exactRationalLiteral (-1247156975557233) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-113380749508164760807) 9830400000000000000000),
            (exactRationalLiteral (1642767608842280743) 102400000000000000000),
            (exactRationalLiteral (-49158519848038759) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (185090835773967001289) 4915200000000000000000),
            (exactRationalLiteral (-2148229605809002857) 51200000000000000000),
            (exactRationalLiteral (28189355822286857) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (284362723555710979831) 2457600000000000000000),
            (exactRationalLiteral (-2565602983382703783) 25600000000000000000),
            (exactRationalLiteral (69524107563014743) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1236700336815270125539) 9830400000000000000000),
            (exactRationalLiteral (16283442762207704963) 102400000000000000000),
            (exactRationalLiteral (-469171943146134307) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-9771329609524136671) 491520000000000000000),
            (exactRationalLiteral (-665945222576801333) 25600000000000000000),
            (exactRationalLiteral (46819684294409413) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (16121438265275794753) 9830400000000000000000),
            (exactRationalLiteral (-1165929350397402049) 102400000000000000000),
            (exactRationalLiteral (5117213653408321) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-796670493191794968413) 3276800000000000000000),
            (exactRationalLiteral (14676361707279775799) 102400000000000000000),
            (exactRationalLiteral (-153255861732877911) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2529981600934670376319) 4915200000000000000000),
            (exactRationalLiteral (-15259455987346942751) 51200000000000000000),
            (exactRationalLiteral (30351798994841843) 320000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-796670493191794968413) 3276800000000000000000),
            (exactRationalLiteral (14676361707279775799) 102400000000000000000),
            (exactRationalLiteral (-153255861732877911) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (16121438265275794753) 9830400000000000000000),
            (exactRationalLiteral (-1165929350397402049) 102400000000000000000),
            (exactRationalLiteral (5117213653408321) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-9771329609524136671) 491520000000000000000),
            (exactRationalLiteral (-665945222576801333) 25600000000000000000),
            (exactRationalLiteral (46819684294409413) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1236700336815270125539) 9830400000000000000000),
            (exactRationalLiteral (16283442762207704963) 102400000000000000000),
            (exactRationalLiteral (-469171943146134307) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (284362723555710979831) 2457600000000000000000),
            (exactRationalLiteral (-2565602983382703783) 25600000000000000000),
            (exactRationalLiteral (69524107563014743) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (185090835773967001289) 4915200000000000000000),
            (exactRationalLiteral (-2148229605809002857) 51200000000000000000),
            (exactRationalLiteral (28189355822286857) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-113380749508164760807) 9830400000000000000000),
            (exactRationalLiteral (1642767608842280743) 102400000000000000000),
            (exactRationalLiteral (-49158519848038759) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-5862414636800065467) 1638400000000000000000),
            (exactRationalLiteral (360463491064201937) 51200000000000000000),
            (exactRationalLiteral (-1247156975557233) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (15060368634410223541) 4915200000000000000000),
            (exactRationalLiteral (227707144607647003) 51200000000000000000),
            (exactRationalLiteral (1092402699477013) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7439179331050060131) 1638400000000000000000),
            (exactRationalLiteral (-93860884298304839) 51200000000000000000),
            (exactRationalLiteral (-3982323836654409) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8056564882619838917) 614400000000000000000),
            (exactRationalLiteral (-20558707754638943) 6400000000000000000),
            (exactRationalLiteral (22295638170883) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (4577513293016655791) 1638400000000000000000),
            (exactRationalLiteral (81266113904280547) 51200000000000000000),
            (exactRationalLiteral (-833175470846163) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (31593348377099086327) 9830400000000000000000),
            (exactRationalLiteral (197936398329396873) 102400000000000000000),
            (exactRationalLiteral (5022523935363319) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6065214634088997167) 9830400000000000000000),
            (exactRationalLiteral (-124913972042259407) 102400000000000000000),
            (exactRationalLiteral (-8813652068769169) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-11309763050569925119) 9830400000000000000000),
            (exactRationalLiteral (409622383388114559) 102400000000000000000),
            (exactRationalLiteral (25342938282194177) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-2076515487851396569) 983040000000000000000),
            (exactRationalLiteral (-1079537044902069187) 51200000000000000000),
            (exactRationalLiteral (-54143927990103869) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7118330917407879233) 1228800000000000000000),
            (exactRationalLiteral (903970550779566329) 12800000000000000000),
            (exactRationalLiteral (52233105397850959) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (56141522461168738171) 819200000000000000000),
            (exactRationalLiteral (-1516964527596801217) 25600000000000000000),
            (exactRationalLiteral (-215610497118452463) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-289627848034840992639) 3276800000000000000000),
            (exactRationalLiteral (-5635561758949302339) 102400000000000000000),
            (exactRationalLiteral (911933341068995331) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (39521919965714119723) 2457600000000000000000),
            (exactRationalLiteral (2507866966559663917) 25600000000000000000),
            (exactRationalLiteral (-117788920291427717) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (24273976954614973501) 1966080000000000000000),
            (exactRationalLiteral (-3657080022218768369) 102400000000000000000),
            (exactRationalLiteral (90025332798886577) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (101673746728037) 327680000000000000000),
            (exactRationalLiteral (-305021240184111) 10240000000000000000),
            (exactRationalLiteral (305021240184111) 320000000000000000),
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
          (exactRationalLiteral (101673746728037) 40960000000000000000),
          (exactRationalLiteral (16574141700572582737) 1228800000000000000000),
          (exactRationalLiteral (5698382773389209) 300000000000000000),
          (exactRationalLiteral (2245579571013551) 25000000000000000),
          (exactRationalLiteral (21542363523175752553) 307200000000000000000),
          (exactRationalLiteral (241891621959531601) 30720000000000000000),
          (exactRationalLiteral (70117963185209) 25000000000000000),
          (exactRationalLiteral (1557955361374611647) 1228800000000000000000),
          (exactRationalLiteral (801734650579223071) 1228800000000000000000),
          (exactRationalLiteral (491369776554449) 150000000000000000),
          (exactRationalLiteral (852892143896321) 300000000000000000),
          (exactRationalLiteral (26426324098173) 2000000000000000),
          (exactRationalLiteral (1380077089899599) 300000000000000000),
          (exactRationalLiteral (192222039291901) 60000000000000000),
          (exactRationalLiteral (2334050981277561761) 614400000000000000000),
          (exactRationalLiteral (14806911273752977991) 1228800000000000000000),
          (exactRationalLiteral (319333236198716811) 8192000000000000000),
          (exactRationalLiteral (36537729829738999679) 307200000000000000000),
          (exactRationalLiteral (160891157966430608467) 1228800000000000000000),
          (exactRationalLiteral (1548364581206023) 75000000000000000),
          (exactRationalLiteral (817545477667799467) 409600000000000000000),
          (exactRationalLiteral (304313879460395598407) 1228800000000000000000),
          (exactRationalLiteral (107342647905643147173) 204800000000000000000),
          (exactRationalLiteral (304313879460395598407) 1228800000000000000000),
          (exactRationalLiteral (817545477667799467) 409600000000000000000),
          (exactRationalLiteral (1548364581206023) 75000000000000000),
          (exactRationalLiteral (160891157966430608467) 1228800000000000000000),
          (exactRationalLiteral (36537729829738999679) 307200000000000000000),
          (exactRationalLiteral (319333236198716811) 8192000000000000000),
          (exactRationalLiteral (14806911273752977991) 1228800000000000000000),
          (exactRationalLiteral (2334050981277561761) 614400000000000000000),
          (exactRationalLiteral (192222039291901) 60000000000000000),
          (exactRationalLiteral (1380077089899599) 300000000000000000),
          (exactRationalLiteral (26426324098173) 2000000000000000),
          (exactRationalLiteral (852892143896321) 300000000000000000),
          (exactRationalLiteral (491369776554449) 150000000000000000),
          (exactRationalLiteral (801734650579223071) 1228800000000000000000),
          (exactRationalLiteral (1557955361374611647) 1228800000000000000000),
          (exactRationalLiteral (70117963185209) 25000000000000000),
          (exactRationalLiteral (241891621959531601) 30720000000000000000),
          (exactRationalLiteral (21542363523175752553) 307200000000000000000),
          (exactRationalLiteral (2245579571013551) 25000000000000000),
          (exactRationalLiteral (5698382773389209) 300000000000000000),
          (exactRationalLiteral (16574141700572582737) 1228800000000000000000),
          (exactRationalLiteral (101673746728037) 40960000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 0),
      (28, 16)
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
theorem generatorCoordinates24_valid : ∀ i, (generatorCoordinates24 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
