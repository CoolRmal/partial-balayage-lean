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

/-- Actual coordinate interval candidates, block 23. -/
def generatorCoordinates23 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 5
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
            (exactRationalLiteral (2745191161656999) 40960000000000000000),
            (exactRationalLiteral (-2745191161656999) 2560000000000000000),
            (exactRationalLiteral (915063720552333) 160000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (4517989521821914511) 245760000000000000000),
            (exactRationalLiteral (-1026413127882093241) 25600000000000000000),
            (exactRationalLiteral (-155417468482829) 1600000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-694368805029299179) 307200000000000000000),
            (exactRationalLiteral (852673886653309053) 6400000000000000000),
            (exactRationalLiteral (-31388397859643371) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-30126321352189058693) 409600000000000000000),
            (exactRationalLiteral (-3334894026788383131) 25600000000000000000),
            (exactRationalLiteral (314434764285925353) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (22036635852708656771) 307200000000000000000),
            (exactRationalLiteral (95543170492183047) 6400000000000000000),
            (exactRationalLiteral (-82108472397327109) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-709400390741349557) 51200000000000000000),
            (exactRationalLiteral (108670029376756041) 3200000000000000000),
            (exactRationalLiteral (20812490628328737) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (16801684441874143) 40960000000000000000),
            (exactRationalLiteral (-147850366150689243) 12800000000000000000),
            (exactRationalLiteral (-21741594034879287) 800000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1960445821109743013) 1228800000000000000000),
            (exactRationalLiteral (45557657074086391) 25600000000000000000),
            (exactRationalLiteral (10067706368079811) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (915387704700598309) 1228800000000000000000),
            (exactRationalLiteral (-11454429240621223) 25600000000000000000),
            (exactRationalLiteral (-3502799473592867) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (3622240643741879629) 1228800000000000000000),
            (exactRationalLiteral (38081117112708177) 25600000000000000000),
            (exactRationalLiteral (2049931020174757) 1600000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1557223263036338071) 614400000000000000000),
            (exactRationalLiteral (22063162447265163) 12800000000000000000),
            (exactRationalLiteral (-282065853054929) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-322809649781234403) 25600000000000000000),
            (exactRationalLiteral (-5149440968477587) 1600000000000000000),
            (exactRationalLiteral (-7242207158301) 100000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-2649233887053525451) 614400000000000000000),
            (exactRationalLiteral (-14230807482764431) 12800000000000000000),
            (exactRationalLiteral (-1702603518397507) 800000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1464864857517437887) 614400000000000000000),
            (exactRationalLiteral (54584419784058787) 12800000000000000000),
            (exactRationalLiteral (390745197402679) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2886466564019692507) 614400000000000000000),
            (exactRationalLiteral (93433738336319673) 12800000000000000000),
            (exactRationalLiteral (-703567740329059) 800000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-17694304950364369469) 1228800000000000000000),
            (exactRationalLiteral (525852550506320927) 25600000000000000000),
            (exactRationalLiteral (-21484999394280917) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (27113701761740697443) 614400000000000000000),
            (exactRationalLiteral (-481587418315568913) 12800000000000000000),
            (exactRationalLiteral (-36282671165816149) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (41534725318020049397) 307200000000000000000),
            (exactRationalLiteral (-1026047323277350447) 6400000000000000000),
            (exactRationalLiteral (119096577191162429) 400000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-64063550999937450891) 409600000000000000000),
            (exactRationalLiteral (6313058049124914427) 25600000000000000000),
            (exactRationalLiteral (-662292971856128121) 1600000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-812693789387503469) 61440000000000000000),
            (exactRationalLiteral (-425947606949614797) 6400000000000000000),
            (exactRationalLiteral (80374678374961079) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (4038544733764077211) 1228800000000000000000),
            (exactRationalLiteral (-219984787976379721) 25600000000000000000),
            (exactRationalLiteral (-31157626675892477) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-327873627488410937053) 1228800000000000000000),
            (exactRationalLiteral (4119126335789144271) 25600000000000000000),
            (exactRationalLiteral (-103386432721241173) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (346411668386644087573) 614400000000000000000),
            (exactRationalLiteral (-4246160570532883319) 12800000000000000000),
            (exactRationalLiteral (19327826398270889) 160000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-327873627488410937053) 1228800000000000000000),
            (exactRationalLiteral (4119126335789144271) 25600000000000000000),
            (exactRationalLiteral (-103386432721241173) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4038544733764077211) 1228800000000000000000),
            (exactRationalLiteral (-219984787976379721) 25600000000000000000),
            (exactRationalLiteral (-31157626675892477) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-812693789387503469) 61440000000000000000),
            (exactRationalLiteral (-425947606949614797) 6400000000000000000),
            (exactRationalLiteral (80374678374961079) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-64063550999937450891) 409600000000000000000),
            (exactRationalLiteral (6313058049124914427) 25600000000000000000),
            (exactRationalLiteral (-662292971856128121) 1600000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (41534725318020049397) 307200000000000000000),
            (exactRationalLiteral (-1026047323277350447) 6400000000000000000),
            (exactRationalLiteral (119096577191162429) 400000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (27113701761740697443) 614400000000000000000),
            (exactRationalLiteral (-481587418315568913) 12800000000000000000),
            (exactRationalLiteral (-36282671165816149) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-17694304950364369469) 1228800000000000000000),
            (exactRationalLiteral (525852550506320927) 25600000000000000000),
            (exactRationalLiteral (-21484999394280917) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-2886466564019692507) 614400000000000000000),
            (exactRationalLiteral (93433738336319673) 12800000000000000000),
            (exactRationalLiteral (-703567740329059) 800000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1464864857517437887) 614400000000000000000),
            (exactRationalLiteral (54584419784058787) 12800000000000000000),
            (exactRationalLiteral (390745197402679) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2649233887053525451) 614400000000000000000),
            (exactRationalLiteral (-14230807482764431) 12800000000000000000),
            (exactRationalLiteral (-1702603518397507) 800000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-322809649781234403) 25600000000000000000),
            (exactRationalLiteral (-5149440968477587) 1600000000000000000),
            (exactRationalLiteral (-7242207158301) 100000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (1557223263036338071) 614400000000000000000),
            (exactRationalLiteral (22063162447265163) 12800000000000000000),
            (exactRationalLiteral (-282065853054929) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3622240643741879629) 1228800000000000000000),
            (exactRationalLiteral (38081117112708177) 25600000000000000000),
            (exactRationalLiteral (2049931020174757) 1600000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (915387704700598309) 1228800000000000000000),
            (exactRationalLiteral (-11454429240621223) 25600000000000000000),
            (exactRationalLiteral (-3502799473592867) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1960445821109743013) 1228800000000000000000),
            (exactRationalLiteral (45557657074086391) 25600000000000000000),
            (exactRationalLiteral (10067706368079811) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (16801684441874143) 40960000000000000000),
            (exactRationalLiteral (-147850366150689243) 12800000000000000000),
            (exactRationalLiteral (-21741594034879287) 800000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-709400390741349557) 51200000000000000000),
            (exactRationalLiteral (108670029376756041) 3200000000000000000),
            (exactRationalLiteral (20812490628328737) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (22036635852708656771) 307200000000000000000),
            (exactRationalLiteral (95543170492183047) 6400000000000000000),
            (exactRationalLiteral (-82108472397327109) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-30126321352189058693) 409600000000000000000),
            (exactRationalLiteral (-3334894026788383131) 25600000000000000000),
            (exactRationalLiteral (314434764285925353) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-694368805029299179) 307200000000000000000),
            (exactRationalLiteral (852673886653309053) 6400000000000000000),
            (exactRationalLiteral (-31388397859643371) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (4517989521821914511) 245760000000000000000),
            (exactRationalLiteral (-1026413127882093241) 25600000000000000000),
            (exactRationalLiteral (-155417468482829) 1600000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2745191161656999) 40960000000000000000),
            (exactRationalLiteral (-2745191161656999) 2560000000000000000),
            (exactRationalLiteral (915063720552333) 160000000000000000),
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
          (exactRationalLiteral (4140988711732296687) 51200000000000000000),
          (exactRationalLiteral (1389035387878932911) 19200000000000000000),
          (exactRationalLiteral (935115395819363) 60000000000000000),
          (exactRationalLiteral (9882558296243923) 9600000000000000000),
          (exactRationalLiteral (32311830911515151) 19200000000000000000),
          (exactRationalLiteral (14681315697281251) 19200000000000000000),
          (exactRationalLiteral (467852290064941399) 153600000000000000000),
          (exactRationalLiteral (67604697669417563) 25600000000000000000),
          (exactRationalLiteral (30746613839378543) 2400000000000000000),
          (exactRationalLiteral (112381230975707631) 25600000000000000000),
          (exactRationalLiteral (203731566865344577) 76800000000000000000),
          (exactRationalLiteral (9902845243595809) 1920000000000000000),
          (exactRationalLiteral (302110623372723119) 19200000000000000000),
          (exactRationalLiteral (148070130539370687) 3200000000000000000),
          (exactRationalLiteral (703185794199835157) 4800000000000000000),
          (exactRationalLiteral (3332621700982323511) 19200000000000000000),
          (exactRationalLiteral (640371708394072631) 38400000000000000000),
          (exactRationalLiteral (23914269397210939) 6400000000000000000),
          (exactRationalLiteral (5321122956166937723) 19200000000000000000),
          (exactRationalLiteral (74885077364170521) 128000000000000000),
          (exactRationalLiteral (5321122956166937723) 19200000000000000000),
          (exactRationalLiteral (23914269397210939) 6400000000000000000),
          (exactRationalLiteral (640371708394072631) 38400000000000000000),
          (exactRationalLiteral (3332621700982323511) 19200000000000000000),
          (exactRationalLiteral (703185794199835157) 4800000000000000000),
          (exactRationalLiteral (148070130539370687) 3200000000000000000),
          (exactRationalLiteral (302110623372723119) 19200000000000000000),
          (exactRationalLiteral (9902845243595809) 1920000000000000000),
          (exactRationalLiteral (203731566865344577) 76800000000000000000),
          (exactRationalLiteral (112381230975707631) 25600000000000000000),
          (exactRationalLiteral (30746613839378543) 2400000000000000000),
          (exactRationalLiteral (67604697669417563) 25600000000000000000),
          (exactRationalLiteral (467852290064941399) 153600000000000000000),
          (exactRationalLiteral (14681315697281251) 19200000000000000000),
          (exactRationalLiteral (32311830911515151) 19200000000000000000),
          (exactRationalLiteral (9882558296243923) 9600000000000000000),
          (exactRationalLiteral (935115395819363) 60000000000000000),
          (exactRationalLiteral (1389035387878932911) 19200000000000000000),
          (exactRationalLiteral (4140988711732296687) 51200000000000000000),
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
      (37, 13),
      (37, 21)
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
            (exactRationalLiteral (101673746728037) 40960000000000000000),
            (exactRationalLiteral (-305021240184111) 2560000000000000000),
            (exactRationalLiteral (305021240184111) 160000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (16574141700572582737) 1228800000000000000000),
            (exactRationalLiteral (-954765863567342769) 25600000000000000000),
            (exactRationalLiteral (7195809925171613) 320000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (3956994341259409127) 307200000000000000000),
            (exactRationalLiteral (683110595557022789) 6400000000000000000),
            (exactRationalLiteral (-53393247688499761) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-35387402981956979743) 409600000000000000000),
            (exactRationalLiteral (-1850703919646966019) 25600000000000000000),
            (exactRationalLiteral (427660289284783203) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (21542363523175752553) 307200000000000000000),
            (exactRationalLiteral (-54801112191232797) 1280000000000000000),
            (exactRationalLiteral (-102665893326846407) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-241891621959531601) 30720000000000000000),
            (exactRationalLiteral (200406491203025777) 3200000000000000000),
            (exactRationalLiteral (25055740284806131) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-913033242567127229) 614400000000000000000),
            (exactRationalLiteral (-243345334226482627) 12800000000000000000),
            (exactRationalLiteral (-5201178000603481) 160000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1557955361374611647) 1228800000000000000000),
            (exactRationalLiteral (89994502983233279) 25600000000000000000),
            (exactRationalLiteral (12150716586493633) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (801734650579223071) 1228800000000000000000),
            (exactRationalLiteral (-26912069632259439) 25600000000000000000),
            (exactRationalLiteral (-4226020722226241) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1292267592564082621) 409600000000000000000),
            (exactRationalLiteral (47018970709418249) 25600000000000000000),
            (exactRationalLiteral (2418995778180279) 1600000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1685786977459691813) 614400000000000000000),
            (exactRationalLiteral (20719664023256403) 12800000000000000000),
            (exactRationalLiteral (-389683358949451) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-999353653556488367) 76800000000000000000),
            (exactRationalLiteral (-5148985755120803) 1600000000000000000),
            (exactRationalLiteral (7469813836693) 100000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-2755973361050657153) 614400000000000000000),
            (exactRationalLiteral (-860116599849679) 512000000000000000),
            (exactRationalLiteral (-386690047668253) 160000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (119837185218539827) 40960000000000000000),
            (exactRationalLiteral (56396130417406827) 12800000000000000000),
            (exactRationalLiteral (515110119271341) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2334050981277561761) 614400000000000000000),
            (exactRationalLiteral (18149490035816829) 2560000000000000000),
            (exactRationalLiteral (-127915267657741) 160000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-14806911273752977991) 1228800000000000000000),
            (exactRationalLiteral (434961736081615719) 25600000000000000000),
            (exactRationalLiteral (-23960407818071687) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (319333236198716811) 8192000000000000000),
            (exactRationalLiteral (-109222868891139637) 2560000000000000000),
            (exactRationalLiteral (4019208095751513) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (36537729829738999679) 307200000000000000000),
            (exactRationalLiteral (-684596251968148823) 6400000000000000000),
            (exactRationalLiteral (51628958463438383) 400000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-160891157966430608467) 1228800000000000000000),
            (exactRationalLiteral (4348217362153299491) 25600000000000000000),
            (exactRationalLiteral (-320127371629679347) 1600000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-5836945924064493571) 307200000000000000000),
            (exactRationalLiteral (-195592631414180677) 6400000000000000000),
            (exactRationalLiteral (34802809392755981) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (817545477667799467) 409600000000000000000),
            (exactRationalLiteral (-290669321075795009) 25600000000000000000),
            (exactRationalLiteral (-4184639873815167) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-304313879460395598407) 1228800000000000000000),
            (exactRationalLiteral (3748394207871863127) 25600000000000000000),
            (exactRationalLiteral (-81979631237399399) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (107342647905643147173) 204800000000000000000),
            (exactRationalLiteral (-3892819457774265279) 12800000000000000000),
            (exactRationalLiteral (3201256975518183) 32000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-304313879460395598407) 1228800000000000000000),
            (exactRationalLiteral (3748394207871863127) 25600000000000000000),
            (exactRationalLiteral (-81979631237399399) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (817545477667799467) 409600000000000000000),
            (exactRationalLiteral (-290669321075795009) 25600000000000000000),
            (exactRationalLiteral (-4184639873815167) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-5836945924064493571) 307200000000000000000),
            (exactRationalLiteral (-195592631414180677) 6400000000000000000),
            (exactRationalLiteral (34802809392755981) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-160891157966430608467) 1228800000000000000000),
            (exactRationalLiteral (4348217362153299491) 25600000000000000000),
            (exactRationalLiteral (-320127371629679347) 1600000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (36537729829738999679) 307200000000000000000),
            (exactRationalLiteral (-684596251968148823) 6400000000000000000),
            (exactRationalLiteral (51628958463438383) 400000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (319333236198716811) 8192000000000000000),
            (exactRationalLiteral (-109222868891139637) 2560000000000000000),
            (exactRationalLiteral (4019208095751513) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-14806911273752977991) 1228800000000000000000),
            (exactRationalLiteral (434961736081615719) 25600000000000000000),
            (exactRationalLiteral (-23960407818071687) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-2334050981277561761) 614400000000000000000),
            (exactRationalLiteral (18149490035816829) 2560000000000000000),
            (exactRationalLiteral (-127915267657741) 160000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (119837185218539827) 40960000000000000000),
            (exactRationalLiteral (56396130417406827) 12800000000000000000),
            (exactRationalLiteral (515110119271341) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2755973361050657153) 614400000000000000000),
            (exactRationalLiteral (-860116599849679) 512000000000000000),
            (exactRationalLiteral (-386690047668253) 160000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-999353653556488367) 76800000000000000000),
            (exactRationalLiteral (-5148985755120803) 1600000000000000000),
            (exactRationalLiteral (7469813836693) 100000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (1685786977459691813) 614400000000000000000),
            (exactRationalLiteral (20719664023256403) 12800000000000000000),
            (exactRationalLiteral (-389683358949451) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1292267592564082621) 409600000000000000000),
            (exactRationalLiteral (47018970709418249) 25600000000000000000),
            (exactRationalLiteral (2418995778180279) 1600000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (801734650579223071) 1228800000000000000000),
            (exactRationalLiteral (-26912069632259439) 25600000000000000000),
            (exactRationalLiteral (-4226020722226241) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1557955361374611647) 1228800000000000000000),
            (exactRationalLiteral (89994502983233279) 25600000000000000000),
            (exactRationalLiteral (12150716586493633) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-913033242567127229) 614400000000000000000),
            (exactRationalLiteral (-243345334226482627) 12800000000000000000),
            (exactRationalLiteral (-5201178000603481) 160000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-241891621959531601) 30720000000000000000),
            (exactRationalLiteral (200406491203025777) 3200000000000000000),
            (exactRationalLiteral (25055740284806131) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (21542363523175752553) 307200000000000000000),
            (exactRationalLiteral (-54801112191232797) 1280000000000000000),
            (exactRationalLiteral (-102665893326846407) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-35387402981956979743) 409600000000000000000),
            (exactRationalLiteral (-1850703919646966019) 25600000000000000000),
            (exactRationalLiteral (427660289284783203) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (3956994341259409127) 307200000000000000000),
            (exactRationalLiteral (683110595557022789) 6400000000000000000),
            (exactRationalLiteral (-53393247688499761) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (16574141700572582737) 1228800000000000000000),
            (exactRationalLiteral (-954765863567342769) 25600000000000000000),
            (exactRationalLiteral (7195809925171613) 320000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (101673746728037) 40960000000000000000),
            (exactRationalLiteral (-305021240184111) 2560000000000000000),
            (exactRationalLiteral (305021240184111) 160000000000000000),
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
          (exactRationalLiteral (5698382773389209) 300000000000000000),
          (exactRationalLiteral (2245579571013551) 25000000000000000),
          (exactRationalLiteral (919444218188686039) 12800000000000000000),
          (exactRationalLiteral (43440799684513891) 3840000000000000000),
          (exactRationalLiteral (70117963185209) 25000000000000000),
          (exactRationalLiteral (224066028209254687) 153600000000000000000),
          (exactRationalLiteral (108769300991704919) 153600000000000000000),
          (exactRationalLiteral (491369776554449) 150000000000000000),
          (exactRationalLiteral (852892143896321) 300000000000000000),
          (exactRationalLiteral (26426324098173) 2000000000000000),
          (exactRationalLiteral (1380077089899599) 300000000000000000),
          (exactRationalLiteral (192222039291901) 60000000000000000),
          (exactRationalLiteral (108676835688779187) 25600000000000000000),
          (exactRationalLiteral (2022805000155018103) 153600000000000000000),
          (exactRationalLiteral (3197530304115915761) 76800000000000000000),
          (exactRationalLiteral (969503481759940583) 7680000000000000000),
          (exactRationalLiteral (21883409370986596171) 153600000000000000000),
          (exactRationalLiteral (1548364581206023) 75000000000000000),
          (exactRationalLiteral (412325497901037409) 153600000000000000000),
          (exactRationalLiteral (13158987682436054453) 51200000000000000000),
          (exactRationalLiteral (41744350027152225127) 76800000000000000000),
          (exactRationalLiteral (13158987682436054453) 51200000000000000000),
          (exactRationalLiteral (412325497901037409) 153600000000000000000),
          (exactRationalLiteral (1548364581206023) 75000000000000000),
          (exactRationalLiteral (21883409370986596171) 153600000000000000000),
          (exactRationalLiteral (969503481759940583) 7680000000000000000),
          (exactRationalLiteral (3197530304115915761) 76800000000000000000),
          (exactRationalLiteral (2022805000155018103) 153600000000000000000),
          (exactRationalLiteral (108676835688779187) 25600000000000000000),
          (exactRationalLiteral (192222039291901) 60000000000000000),
          (exactRationalLiteral (1380077089899599) 300000000000000000),
          (exactRationalLiteral (26426324098173) 2000000000000000),
          (exactRationalLiteral (852892143896321) 300000000000000000),
          (exactRationalLiteral (491369776554449) 150000000000000000),
          (exactRationalLiteral (108769300991704919) 153600000000000000000),
          (exactRationalLiteral (224066028209254687) 153600000000000000000),
          (exactRationalLiteral (70117963185209) 25000000000000000),
          (exactRationalLiteral (43440799684513891) 3840000000000000000),
          (exactRationalLiteral (919444218188686039) 12800000000000000000),
          (exactRationalLiteral (2245579571013551) 25000000000000000),
          (exactRationalLiteral (5698382773389209) 300000000000000000),
          (exactRationalLiteral (2441038650825626849) 153600000000000000000),
          (exactRationalLiteral (101673746728037) 5120000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 12),
      (37, 20)
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
            (exactRationalLiteral (3028962588774950267) 327680000000000000000),
            (exactRationalLiteral (-293125411816930671) 10240000000000000000),
            (exactRationalLiteral (9455658445707441) 320000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (41152035911231141923) 1966080000000000000000),
            (exactRationalLiteral (7201910202301439311) 102400000000000000000),
            (exactRationalLiteral (-451991673616226833) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-207150719121949203707) 2457600000000000000000),
            (exactRationalLiteral (-326980238940048563) 25600000000000000000),
            (exactRationalLiteral (212283827141418133) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (190664149200873550431) 3276800000000000000000),
            (exactRationalLiteral (-9400075973602989699) 102400000000000000000),
            (exactRationalLiteral (-786449533913872419) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (109405065302398981) 819200000000000000000),
            (exactRationalLiteral (2168825881226662463) 25600000000000000000),
            (exactRationalLiteral (92750816824337007) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-4730166275816078543) 1228800000000000000000),
            (exactRationalLiteral (-320553427676663911) 12800000000000000000),
            (exactRationalLiteral (-11415639449309951) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-368970680297321863) 983040000000000000000),
            (exactRationalLiteral (250165448842009853) 51200000000000000000),
            (exactRationalLiteral (9820511531967901) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7870482142162554529) 9830400000000000000000),
            (exactRationalLiteral (-173599315257316161) 102400000000000000000),
            (exactRationalLiteral (-5902214994013153) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (3274098388766136497) 9830400000000000000000),
            (exactRationalLiteral (78455590198872433) 102400000000000000000),
            (exactRationalLiteral (2034666660731441) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (22357512919859782057) 9830400000000000000000),
            (exactRationalLiteral (62664103310082633) 102400000000000000000),
            (exactRationalLiteral (-513447434719511) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1873950728652041681) 1638400000000000000000),
            (exactRationalLiteral (82828764502515427) 51200000000000000000),
            (exactRationalLiteral (781087117571667) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6344695245073368947) 614400000000000000000),
            (exactRationalLiteral (-15276036597144623) 6400000000000000000),
            (exactRationalLiteral (-198384676754027) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-7168634015342972061) 1638400000000000000000),
            (exactRationalLiteral (41197521926268601) 51200000000000000000),
            (exactRationalLiteral (-519623037498039) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4162713536917008629) 4915200000000000000000),
            (exactRationalLiteral (218127197479924123) 51200000000000000000),
            (exactRationalLiteral (-773071128552917) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-18086721955909226277) 1638400000000000000000),
            (exactRationalLiteral (464089040515795217) 51200000000000000000),
            (exactRationalLiteral (-2207028006162543) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-360539824172499281977) 9830400000000000000000),
            (exactRationalLiteral (3478345009018759783) 102400000000000000000),
            (exactRationalLiteral (-12027393491177209) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-89532609014211664681) 4915200000000000000000),
            (exactRationalLiteral (14296254712559233623) 51200000000000000000),
            (exactRationalLiteral (-576338833101228073) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1613794935304568747401) 2457600000000000000000),
            (exactRationalLiteral (-37097477864639409063) 25600000000000000000),
            (exactRationalLiteral (1081538388478875433) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-8588210034965584650109) 9830400000000000000000),
            (exactRationalLiteral (198408279452877711683) 102400000000000000000),
            (exactRationalLiteral (-5601655946542865917) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (150542360167793134943) 491520000000000000000),
            (exactRationalLiteral (-23982467322233660213) 25600000000000000000),
            (exactRationalLiteral (730397719027485883) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-229263765162799239137) 9830400000000000000000),
            (exactRationalLiteral (10664881891332888191) 102400000000000000000),
            (exactRationalLiteral (-399477588377751329) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-1471222226647066345283) 3276800000000000000000),
            (exactRationalLiteral (33504774078981248759) 102400000000000000000),
            (exactRationalLiteral (-474357883990504521) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4537285978872158349409) 4915200000000000000000),
            (exactRationalLiteral (-31838464107329437151) 51200000000000000000),
            (exactRationalLiteral (80174921805041453) 320000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-1471222226647066345283) 3276800000000000000000),
            (exactRationalLiteral (33504774078981248759) 102400000000000000000),
            (exactRationalLiteral (-474357883990504521) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-229263765162799239137) 9830400000000000000000),
            (exactRationalLiteral (10664881891332888191) 102400000000000000000),
            (exactRationalLiteral (-399477588377751329) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (150542360167793134943) 491520000000000000000),
            (exactRationalLiteral (-23982467322233660213) 25600000000000000000),
            (exactRationalLiteral (730397719027485883) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-8588210034965584650109) 9830400000000000000000),
            (exactRationalLiteral (198408279452877711683) 102400000000000000000),
            (exactRationalLiteral (-5601655946542865917) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1613794935304568747401) 2457600000000000000000),
            (exactRationalLiteral (-37097477864639409063) 25600000000000000000),
            (exactRationalLiteral (1081538388478875433) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-89532609014211664681) 4915200000000000000000),
            (exactRationalLiteral (14296254712559233623) 51200000000000000000),
            (exactRationalLiteral (-576338833101228073) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-360539824172499281977) 9830400000000000000000),
            (exactRationalLiteral (3478345009018759783) 102400000000000000000),
            (exactRationalLiteral (-12027393491177209) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-18086721955909226277) 1638400000000000000000),
            (exactRationalLiteral (464089040515795217) 51200000000000000000),
            (exactRationalLiteral (-2207028006162543) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4162713536917008629) 4915200000000000000000),
            (exactRationalLiteral (218127197479924123) 51200000000000000000),
            (exactRationalLiteral (-773071128552917) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7168634015342972061) 1638400000000000000000),
            (exactRationalLiteral (41197521926268601) 51200000000000000000),
            (exactRationalLiteral (-519623037498039) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6344695245073368947) 614400000000000000000),
            (exactRationalLiteral (-15276036597144623) 6400000000000000000),
            (exactRationalLiteral (-198384676754027) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (1873950728652041681) 1638400000000000000000),
            (exactRationalLiteral (82828764502515427) 51200000000000000000),
            (exactRationalLiteral (781087117571667) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (22357512919859782057) 9830400000000000000000),
            (exactRationalLiteral (62664103310082633) 102400000000000000000),
            (exactRationalLiteral (-513447434719511) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3274098388766136497) 9830400000000000000000),
            (exactRationalLiteral (78455590198872433) 102400000000000000000),
            (exactRationalLiteral (2034666660731441) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-7870482142162554529) 9830400000000000000000),
            (exactRationalLiteral (-173599315257316161) 102400000000000000000),
            (exactRationalLiteral (-5902214994013153) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-368970680297321863) 983040000000000000000),
            (exactRationalLiteral (250165448842009853) 51200000000000000000),
            (exactRationalLiteral (9820511531967901) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4730166275816078543) 1228800000000000000000),
            (exactRationalLiteral (-320553427676663911) 12800000000000000000),
            (exactRationalLiteral (-11415639449309951) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (109405065302398981) 819200000000000000000),
            (exactRationalLiteral (2168825881226662463) 25600000000000000000),
            (exactRationalLiteral (92750816824337007) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (190664149200873550431) 3276800000000000000000),
            (exactRationalLiteral (-9400075973602989699) 102400000000000000000),
            (exactRationalLiteral (-786449533913872419) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-207150719121949203707) 2457600000000000000000),
            (exactRationalLiteral (-326980238940048563) 25600000000000000000),
            (exactRationalLiteral (212283827141418133) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (41152035911231141923) 1966080000000000000000),
            (exactRationalLiteral (7201910202301439311) 102400000000000000000),
            (exactRationalLiteral (-451991673616226833) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (3028962588774950267) 327680000000000000000),
            (exactRationalLiteral (-293125411816930671) 10240000000000000000),
            (exactRationalLiteral (9455658445707441) 320000000000000000),
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
          (exactRationalLiteral (28253500296969814687) 1228800000000000000000),
          (exactRationalLiteral (6489968148847382569) 76800000000000000000),
          (exactRationalLiteral (6080899191886277) 100000000000000000),
          (exactRationalLiteral (887833322449429463) 307200000000000000000),
          (exactRationalLiteral (238497993848573393) 51200000000000000000),
          (exactRationalLiteral (19559906505071) 37500000000000000),
          (exactRationalLiteral (210198630695183389) 245760000000000000000),
          (exactRationalLiteral (439400943590078929) 1228800000000000000000),
          (exactRationalLiteral (2818018677483109273) 1228800000000000000000),
          (exactRationalLiteral (734078491507929883) 614400000000000000000),
          (exactRationalLiteral (10651851921474279) 1024000000000000000),
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
          (exactRationalLiteral (10651851921474279) 1024000000000000000),
          (exactRationalLiteral (734078491507929883) 614400000000000000000),
          (exactRationalLiteral (2818018677483109273) 1228800000000000000000),
          (exactRationalLiteral (439400943590078929) 1228800000000000000000),
          (exactRationalLiteral (210198630695183389) 245760000000000000000),
          (exactRationalLiteral (19559906505071) 37500000000000000),
          (exactRationalLiteral (238497993848573393) 51200000000000000000),
          (exactRationalLiteral (887833322449429463) 307200000000000000000),
          (exactRationalLiteral (6080899191886277) 100000000000000000),
          (exactRationalLiteral (6489968148847382569) 76800000000000000000),
          (exactRationalLiteral (28253500296969814687) 1228800000000000000000),
          (exactRationalLiteral (101673746728037) 10000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 15),
      (28, 31)
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
            (exactRationalLiteral (2479721008950094393) 327680000000000000000),
            (exactRationalLiteral (-256522862994837351) 10240000000000000000),
            (exactRationalLiteral (8845615965339219) 320000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (243692278554946987061) 9830400000000000000000),
            (exactRationalLiteral (5466212442025213767) 102400000000000000000),
            (exactRationalLiteral (-415857206521885939) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-206653214029207903049) 2457600000000000000000),
            (exactRationalLiteral (478145369967911189) 25600000000000000000),
            (exactRationalLiteral (190278977312561743) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (168869166484677225157) 3276800000000000000000),
            (exactRationalLiteral (-492776922370430547) 4096000000000000000),
            (exactRationalLiteral (-673224008915014569) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (14371950601441138613) 2457600000000000000000),
            (exactRationalLiteral (499742861332994379) 5120000000000000000),
            (exactRationalLiteral (72193395894817709) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1354700303328374369) 245760000000000000000),
            (exactRationalLiteral (-357729486160948927) 12800000000000000000),
            (exactRationalLiteral (-7172389792832557) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-243071753923487857) 4915200000000000000000),
            (exactRationalLiteral (280918903033605221) 51200000000000000000),
            (exactRationalLiteral (5556215563829783) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8974572572760954043) 9830400000000000000000),
            (exactRationalLiteral (-193042154796541129) 102400000000000000000),
            (exactRationalLiteral (-3819204775599331) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (3766355044893614891) 9830400000000000000000),
            (exactRationalLiteral (85147814344531449) 102400000000000000000),
            (exactRationalLiteral (1311445412098067) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (7576270809845221937) 3276800000000000000000),
            (exactRationalLiteral (61348443087215633) 102400000000000000000),
            (exactRationalLiteral (-144382676713989) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6127767348358499521) 4915200000000000000000),
            (exactRationalLiteral (85737877961013051) 51200000000000000000),
            (exactRationalLiteral (134693922335429) 320000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6438673232693305033) 614400000000000000000),
            (exactRationalLiteral (-16040151262170743) 6400000000000000000),
            (exactRationalLiteral (-183672655759033) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-21265875777801056077) 4915200000000000000000),
            (exactRationalLiteral (38657336336388929) 51200000000000000000),
            (exactRationalLiteral (-750469757441797) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-954243248630874749) 1638400000000000000000),
            (exactRationalLiteral (215283642809449779) 51200000000000000000),
            (exactRationalLiteral (-129741241336851) 320000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-51501859995098696629) 4915200000000000000000),
            (exactRationalLiteral (455388911295225753) 51200000000000000000),
            (exactRationalLiteral (-2143036604122189) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-339823984473976012867) 9830400000000000000000),
            (exactRationalLiteral (3425284618206469407) 102400000000000000000),
            (exactRationalLiteral (-14502801914967979) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-3503313073008243057) 1638400000000000000000),
            (exactRationalLiteral (2414300627735491331) 10240000000000000000),
            (exactRationalLiteral (-536036953839660411) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (280783731660713580407) 491520000000000000000),
            (exactRationalLiteral (-32906259548179355423) 25600000000000000000),
            (exactRationalLiteral (1014070769751151387) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-7463611567205926975919) 9830400000000000000000),
            (exactRationalLiteral (176685986867159145563) 102400000000000000000),
            (exactRationalLiteral (-5259490346316417143) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (617399482057964723641) 2457600000000000000000),
            (exactRationalLiteral (-21152020184088126877) 25600000000000000000),
            (exactRationalLiteral (136965170009056157) 160000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-56653437642708872233) 3276800000000000000000),
            (exactRationalLiteral (1824183502285207499) 20480000000000000000),
            (exactRationalLiteral (-372504601575674019) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-4218244702869262230451) 9830400000000000000000),
            (exactRationalLiteral (31650156145986914223) 102400000000000000000),
            (exactRationalLiteral (-452951082506662747) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1450333086235356871401) 1638400000000000000000),
            (exactRationalLiteral (-30268181086435407831) 51200000000000000000),
            (exactRationalLiteral (76853380284361479) 320000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-4218244702869262230451) 9830400000000000000000),
            (exactRationalLiteral (31650156145986914223) 102400000000000000000),
            (exactRationalLiteral (-452951082506662747) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-56653437642708872233) 3276800000000000000000),
            (exactRationalLiteral (1824183502285207499) 20480000000000000000),
            (exactRationalLiteral (-372504601575674019) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (617399482057964723641) 2457600000000000000000),
            (exactRationalLiteral (-21152020184088126877) 25600000000000000000),
            (exactRationalLiteral (136965170009056157) 160000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-7463611567205926975919) 9830400000000000000000),
            (exactRationalLiteral (176685986867159145563) 102400000000000000000),
            (exactRationalLiteral (-5259490346316417143) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (280783731660713580407) 491520000000000000000),
            (exactRationalLiteral (-32906259548179355423) 25600000000000000000),
            (exactRationalLiteral (1014070769751151387) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-3503313073008243057) 1638400000000000000000),
            (exactRationalLiteral (2414300627735491331) 10240000000000000000),
            (exactRationalLiteral (-536036953839660411) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-339823984473976012867) 9830400000000000000000),
            (exactRationalLiteral (3425284618206469407) 102400000000000000000),
            (exactRationalLiteral (-14502801914967979) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-51501859995098696629) 4915200000000000000000),
            (exactRationalLiteral (455388911295225753) 51200000000000000000),
            (exactRationalLiteral (-2143036604122189) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-954243248630874749) 1638400000000000000000),
            (exactRationalLiteral (215283642809449779) 51200000000000000000),
            (exactRationalLiteral (-129741241336851) 320000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-21265875777801056077) 4915200000000000000000),
            (exactRationalLiteral (38657336336388929) 51200000000000000000),
            (exactRationalLiteral (-750469757441797) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6438673232693305033) 614400000000000000000),
            (exactRationalLiteral (-16040151262170743) 6400000000000000000),
            (exactRationalLiteral (-183672655759033) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (6127767348358499521) 4915200000000000000000),
            (exactRationalLiteral (85737877961013051) 51200000000000000000),
            (exactRationalLiteral (134693922335429) 320000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (7576270809845221937) 3276800000000000000000),
            (exactRationalLiteral (61348443087215633) 102400000000000000000),
            (exactRationalLiteral (-144382676713989) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3766355044893614891) 9830400000000000000000),
            (exactRationalLiteral (85147814344531449) 102400000000000000000),
            (exactRationalLiteral (1311445412098067) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-8974572572760954043) 9830400000000000000000),
            (exactRationalLiteral (-193042154796541129) 102400000000000000000),
            (exactRationalLiteral (-3819204775599331) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-243071753923487857) 4915200000000000000000),
            (exactRationalLiteral (280918903033605221) 51200000000000000000),
            (exactRationalLiteral (5556215563829783) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1354700303328374369) 245760000000000000000),
            (exactRationalLiteral (-357729486160948927) 12800000000000000000),
            (exactRationalLiteral (-7172389792832557) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (14371950601441138613) 2457600000000000000000),
            (exactRationalLiteral (499742861332994379) 5120000000000000000),
            (exactRationalLiteral (72193395894817709) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (168869166484677225157) 3276800000000000000000),
            (exactRationalLiteral (-492776922370430547) 4096000000000000000),
            (exactRationalLiteral (-673224008915014569) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-206653214029207903049) 2457600000000000000000),
            (exactRationalLiteral (478145369967911189) 25600000000000000000),
            (exactRationalLiteral (190278977312561743) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (243692278554946987061) 9830400000000000000000),
            (exactRationalLiteral (5466212442025213767) 102400000000000000000),
            (exactRationalLiteral (-415857206521885939) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2479721008950094393) 327680000000000000000),
            (exactRationalLiteral (-256522862994837351) 10240000000000000000),
            (exactRationalLiteral (8845615965339219) 320000000000000000),
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
          (exactRationalLiteral (2745191161656999) 327680000000000000),
          (exactRationalLiteral (4044709554609439703) 153600000000000000000),
          (exactRationalLiteral (25938226347782440399) 307200000000000000000),
          (exactRationalLiteral (22562061826773728911) 409600000000000000000),
          (exactRationalLiteral (114970807284665353) 12800000000000000000),
          (exactRationalLiteral (4916303449796861) 768000000000000000),
          (exactRationalLiteral (44459486181197713) 204800000000000000000),
          (exactRationalLiteral (149439299162002633) 153600000000000000000),
          (exactRationalLiteral (62896425211549793) 153600000000000000000),
          (exactRationalLiteral (358009517861658961) 153600000000000000000),
          (exactRationalLiteral (33265351991268869) 25600000000000000000),
          (exactRationalLiteral (50682323034660913) 4800000000000000000),
          (exactRationalLiteral (2672997971590322047) 614400000000000000000),
          (exactRationalLiteral (87764724385049017) 122880000000000000000),
          (exactRationalLiteral (6609310979312220079) 614400000000000000000),
          (exactRationalLiteral (8753552725753210741) 245760000000000000000),
          (exactRationalLiteral (241763552181034321) 24576000000000000000),
          (exactRationalLiteral (188214172883340410561) 307200000000000000000),
          (exactRationalLiteral (333734128401936120351) 409600000000000000000),
          (exactRationalLiteral (85366600761857006147) 307200000000000000000),
          (exactRationalLiteral (24806758220066598737) 1228800000000000000000),
          (exactRationalLiteral (539320590994435610281) 1228800000000000000000),
          (exactRationalLiteral (555370613315430494977) 614400000000000000000),
          (exactRationalLiteral (539320590994435610281) 1228800000000000000000),
          (exactRationalLiteral (24806758220066598737) 1228800000000000000000),
          (exactRationalLiteral (85366600761857006147) 307200000000000000000),
          (exactRationalLiteral (333734128401936120351) 409600000000000000000),
          (exactRationalLiteral (188214172883340410561) 307200000000000000000),
          (exactRationalLiteral (241763552181034321) 24576000000000000000),
          (exactRationalLiteral (8753552725753210741) 245760000000000000000),
          (exactRationalLiteral (6609310979312220079) 614400000000000000000),
          (exactRationalLiteral (87764724385049017) 122880000000000000000),
          (exactRationalLiteral (2672997971590322047) 614400000000000000000),
          (exactRationalLiteral (50682323034660913) 4800000000000000000),
          (exactRationalLiteral (33265351991268869) 25600000000000000000),
          (exactRationalLiteral (358009517861658961) 153600000000000000000),
          (exactRationalLiteral (62896425211549793) 153600000000000000000),
          (exactRationalLiteral (149439299162002633) 153600000000000000000),
          (exactRationalLiteral (44459486181197713) 204800000000000000000),
          (exactRationalLiteral (4916303449796861) 768000000000000000),
          (exactRationalLiteral (114970807284665353) 12800000000000000000),
          (exactRationalLiteral (22562061826773728911) 409600000000000000000),
          (exactRationalLiteral (25938226347782440399) 307200000000000000000),
          (exactRationalLiteral (4044709554609439703) 153600000000000000000),
          (exactRationalLiteral (2745191161656999) 327680000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 14),
      (28, 30)
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
            (exactRationalLiteral (1237064476440026179) 327680000000000000000),
            (exactRationalLiteral (-161356236057394719) 10240000000000000000),
            (exactRationalLiteral (7015488524234553) 320000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (301074046653225970007) 9830400000000000000000),
            (exactRationalLiteral (1126346371460718591) 102400000000000000000),
            (exactRationalLiteral (-307453805238863257) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-179872991601545323523) 2457600000000000000000),
            (exactRationalLiteral (473081160159847417) 5120000000000000000),
            (exactRationalLiteral (124264427825992573) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (74792682708131001223) 3276800000000000000000),
            (exactRationalLiteral (-18360051716261497203) 102400000000000000000),
            (exactRationalLiteral (-333547433918441019) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (64925493417662861111) 2457600000000000000000),
            (exactRationalLiteral (2995001480671437039) 25600000000000000000),
            (exactRationalLiteral (2104226621251963) 160000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2705795880453062027) 245760000000000000000),
            (exactRationalLiteral (-367419669858346519) 12800000000000000000),
            (exactRationalLiteral (44458873412797) 3200000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (4952995817016105941) 4915200000000000000000),
            (exactRationalLiteral (270836162373076493) 51200000000000000000),
            (exactRationalLiteral (-7236672340584571) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-12636840371274729337) 9830400000000000000000),
            (exactRationalLiteral (-40275685634456861) 20480000000000000000),
            (exactRationalLiteral (485965175928427) 640000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (5362543912749367817) 9830400000000000000000),
            (exactRationalLiteral (87867176814307521) 102400000000000000000),
            (exactRationalLiteral (-171643666760411) 640000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (7952450023295010923) 3276800000000000000000),
            (exactRationalLiteral (66259016610747161) 102400000000000000000),
            (exactRationalLiteral (962811597302577) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (7732161179081257723) 4915200000000000000000),
            (exactRationalLiteral (18376479639007479) 10240000000000000000),
            (exactRationalLiteral (350617093993579) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6745643703966894619) 614400000000000000000),
            (exactRationalLiteral (-17979406753369247) 6400000000000000000),
            (exactRationalLiteral (-139536592774051) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-4135205180660739059) 983040000000000000000),
            (exactRationalLiteral (25496458288099721) 51200000000000000000),
            (exactRationalLiteral (-1443009917273071) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (318582321972462577) 1638400000000000000000),
            (exactRationalLiteral (41947547384574927) 10240000000000000000),
            (exactRationalLiteral (-275611441078269) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8705879294721894251) 983040000000000000000),
            (exactRationalLiteral (430824317282485857) 51200000000000000000),
            (exactRationalLiteral (-1951062398001127) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-280002508062845508433) 9830400000000000000000),
            (exactRationalLiteral (3206693643598619799) 102400000000000000000),
            (exactRationalLiteral (-21929027186340289) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (51079243074245157909) 1638400000000000000000),
            (exactRationalLiteral (6364493519309749639) 51200000000000000000),
            (exactRationalLiteral (-16605252642198297) 64000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (913839126746869657249) 2457600000000000000000),
            (exactRationalLiteral (-21951827448264571607) 25600000000000000000),
            (exactRationalLiteral (811667913567979249) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-4814334876174778939637) 9830400000000000000000),
            (exactRationalLiteral (119731083515438217779) 102400000000000000000),
            (exactRationalLiteral (-4232993545637070821) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (305702548699190614051) 2457600000000000000000),
            (exactRationalLiteral (-13754403625224449221) 25600000000000000000),
            (exactRationalLiteral (548110243098665491) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-14367070706002128787) 3276800000000000000000),
            (exactRationalLiteral (5136376054955340847) 102400000000000000000),
            (exactRationalLiteral (-291585641169442089) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-3695148674591962439521) 9830400000000000000000),
            (exactRationalLiteral (26600065582616113191) 102400000000000000000),
            (exactRationalLiteral (-15549227122205497) 128000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (256391946138841419063) 327680000000000000000),
            (exactRationalLiteral (-25955917006234916751) 51200000000000000000),
            (exactRationalLiteral (66888755722321557) 320000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-3695148674591962439521) 9830400000000000000000),
            (exactRationalLiteral (26600065582616113191) 102400000000000000000),
            (exactRationalLiteral (-15549227122205497) 128000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-14367070706002128787) 3276800000000000000000),
            (exactRationalLiteral (5136376054955340847) 102400000000000000000),
            (exactRationalLiteral (-291585641169442089) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (305702548699190614051) 2457600000000000000000),
            (exactRationalLiteral (-13754403625224449221) 25600000000000000000),
            (exactRationalLiteral (548110243098665491) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-4814334876174778939637) 9830400000000000000000),
            (exactRationalLiteral (119731083515438217779) 102400000000000000000),
            (exactRationalLiteral (-4232993545637070821) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (913839126746869657249) 2457600000000000000000),
            (exactRationalLiteral (-21951827448264571607) 25600000000000000000),
            (exactRationalLiteral (811667913567979249) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (51079243074245157909) 1638400000000000000000),
            (exactRationalLiteral (6364493519309749639) 51200000000000000000),
            (exactRationalLiteral (-16605252642198297) 64000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-280002508062845508433) 9830400000000000000000),
            (exactRationalLiteral (3206693643598619799) 102400000000000000000),
            (exactRationalLiteral (-21929027186340289) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-8705879294721894251) 983040000000000000000),
            (exactRationalLiteral (430824317282485857) 51200000000000000000),
            (exactRationalLiteral (-1951062398001127) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (318582321972462577) 1638400000000000000000),
            (exactRationalLiteral (41947547384574927) 10240000000000000000),
            (exactRationalLiteral (-275611441078269) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4135205180660739059) 983040000000000000000),
            (exactRationalLiteral (25496458288099721) 51200000000000000000),
            (exactRationalLiteral (-1443009917273071) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6745643703966894619) 614400000000000000000),
            (exactRationalLiteral (-17979406753369247) 6400000000000000000),
            (exactRationalLiteral (-139536592774051) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (7732161179081257723) 4915200000000000000000),
            (exactRationalLiteral (18376479639007479) 10240000000000000000),
            (exactRationalLiteral (350617093993579) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (7952450023295010923) 3276800000000000000000),
            (exactRationalLiteral (66259016610747161) 102400000000000000000),
            (exactRationalLiteral (962811597302577) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5362543912749367817) 9830400000000000000000),
            (exactRationalLiteral (87867176814307521) 102400000000000000000),
            (exactRationalLiteral (-171643666760411) 640000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-12636840371274729337) 9830400000000000000000),
            (exactRationalLiteral (-40275685634456861) 20480000000000000000),
            (exactRationalLiteral (485965175928427) 640000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (4952995817016105941) 4915200000000000000000),
            (exactRationalLiteral (270836162373076493) 51200000000000000000),
            (exactRationalLiteral (-7236672340584571) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2705795880453062027) 245760000000000000000),
            (exactRationalLiteral (-367419669858346519) 12800000000000000000),
            (exactRationalLiteral (44458873412797) 3200000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (64925493417662861111) 2457600000000000000000),
            (exactRationalLiteral (2995001480671437039) 25600000000000000000),
            (exactRationalLiteral (2104226621251963) 160000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (74792682708131001223) 3276800000000000000000),
            (exactRationalLiteral (-18360051716261497203) 102400000000000000000),
            (exactRationalLiteral (-333547433918441019) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-179872991601545323523) 2457600000000000000000),
            (exactRationalLiteral (473081160159847417) 5120000000000000000),
            (exactRationalLiteral (124264427825992573) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (301074046653225970007) 9830400000000000000000),
            (exactRationalLiteral (1126346371460718591) 102400000000000000000),
            (exactRationalLiteral (-307453805238863257) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1237064476440026179) 327680000000000000000),
            (exactRationalLiteral (-161356236057394719) 10240000000000000000),
            (exactRationalLiteral (7015488524234553) 320000000000000000),
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
          (exactRationalLiteral (37943598948179838307) 1228800000000000000000),
          (exactRationalLiteral (182212317671436161) 2400000000000000000),
          (exactRationalLiteral (181250617323517411) 6400000000000000000),
          (exactRationalLiteral (3080490939522133001) 102400000000000000000),
          (exactRationalLiteral (365311117737057803) 30720000000000000000),
          (exactRationalLiteral (717707767391189081) 614400000000000000000),
          (exactRationalLiteral (1654080584130431117) 1228800000000000000000),
          (exactRationalLiteral (702901147195820941) 1228800000000000000000),
          (exactRationalLiteral (3007400010861023093) 1228800000000000000000),
          (exactRationalLiteral (333700267341475141) 204800000000000000000),
          (exactRationalLiteral (849999147249353377) 76800000000000000000),
          (exactRationalLiteral (40540486102655941) 9600000000000000000),
          (exactRationalLiteral (39604888120592779) 122880000000000000000),
          (exactRationalLiteral (87554208219437407) 9600000000000000000),
          (exactRationalLiteral (565795192130836901) 19200000000000000000),
          (exactRationalLiteral (855529833860653171) 24576000000000000000),
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
          (exactRationalLiteral (855529833860653171) 24576000000000000000),
          (exactRationalLiteral (565795192130836901) 19200000000000000000),
          (exactRationalLiteral (87554208219437407) 9600000000000000000),
          (exactRationalLiteral (39604888120592779) 122880000000000000000),
          (exactRationalLiteral (40540486102655941) 9600000000000000000),
          (exactRationalLiteral (849999147249353377) 76800000000000000000),
          (exactRationalLiteral (333700267341475141) 204800000000000000000),
          (exactRationalLiteral (3007400010861023093) 1228800000000000000000),
          (exactRationalLiteral (702901147195820941) 1228800000000000000000),
          (exactRationalLiteral (1654080584130431117) 1228800000000000000000),
          (exactRationalLiteral (717707767391189081) 614400000000000000000),
          (exactRationalLiteral (365311117737057803) 30720000000000000000),
          (exactRationalLiteral (3080490939522133001) 102400000000000000000),
          (exactRationalLiteral (181250617323517411) 6400000000000000000),
          (exactRationalLiteral (182212317671436161) 2400000000000000000),
          (exactRationalLiteral (37943598948179838307) 1228800000000000000000),
          (exactRationalLiteral (2745191161656999) 640000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 11),
      (28, 27)
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
            (exactRationalLiteral (941600568448350657) 327680000000000000000),
            (exactRationalLiteral (-134514366921192951) 10240000000000000000),
            (exactRationalLiteral (6405446043866331) 320000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (60857443417500257209) 1966080000000000000000),
            (exactRationalLiteral (-31199915306052649) 102400000000000000000),
            (exactRationalLiteral (-271319338144522363) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-164277403062153415697) 2457600000000000000000),
            (exactRationalLiteral (2818453812445494597) 25600000000000000000),
            (exactRationalLiteral (102259577997136183) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (36889356906599386541) 3276800000000000000000),
            (exactRationalLiteral (-19467790401937545579) 102400000000000000000),
            (exactRationalLiteral (-220321908919583169) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (82939526215248523933) 2457600000000000000000),
            (exactRationalLiteral (2995971171237437703) 25600000000000000000),
            (exactRationalLiteral (-10036287823259483) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-5216612037556761391) 409600000000000000000),
            (exactRationalLiteral (-336703733838993231) 12800000000000000000),
            (exactRationalLiteral (9800608833077019) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (86321540523933301) 65536000000000000000),
            (exactRationalLiteral (233360881074461973) 51200000000000000000),
            (exactRationalLiteral (-11500968308722689) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-13807620988879074259) 9830400000000000000000),
            (exactRationalLiteral (-187493104216888121) 102400000000000000000),
            (exactRationalLiteral (4512836098055957) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (5876555468635054787) 9830400000000000000000),
            (exactRationalLiteral (82987860981832553) 102400000000000000000),
            (exactRationalLiteral (-1581439582435429) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (24267934167749168747) 9830400000000000000000),
            (exactRationalLiteral (70848392515968513) 102400000000000000000),
            (exactRationalLiteral (1331876355308099) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (8287232503355826953) 4915200000000000000000),
            (exactRationalLiteral (93069631559222667) 51200000000000000000),
            (exactRationalLiteral (242999588099057) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2285045245172139579) 204800000000000000000),
            (exactRationalLiteral (-18508129082475463) 6400000000000000000),
            (exactRationalLiteral (-124824571779057) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-20541286659462148853) 4915200000000000000000),
            (exactRationalLiteral (19262725179119921) 51200000000000000000),
            (exactRationalLiteral (-1673856637216829) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2211363509849170961) 4915200000000000000000),
            (exactRationalLiteral (208884021002298883) 51200000000000000000),
            (exactRationalLiteral (-151246519209607) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-40967607353082408221) 4915200000000000000000),
            (exactRationalLiteral (423148050494562057) 51200000000000000000),
            (exactRationalLiteral (-1887070995960773) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-261035396161185036187) 9830400000000000000000),
            (exactRationalLiteral (3114026718005677103) 102400000000000000000),
            (exactRationalLiteral (-24404435610131059) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (186604322062980753109) 4915200000000000000000),
            (exactRationalLiteral (4784572013613055263) 51200000000000000000),
            (exactRationalLiteral (-374829436793389763) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (791598306545187082411) 2457600000000000000000),
            (exactRationalLiteral (-18840091031448102703) 25600000000000000000),
            (exactRationalLiteral (744200294840255203) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1381791878409629562573) 3276800000000000000000),
            (exactRationalLiteral (103483440533342832043) 102400000000000000000),
            (exactRationalLiteral (-3890827945410622047) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9182846495563963369) 98304000000000000000),
            (exactRationalLiteral (-11653106390794197453) 25600000000000000000),
            (exactRationalLiteral (502538374116460393) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-15674091535099337107) 9830400000000000000000),
            (exactRationalLiteral (4023979463881727111) 102400000000000000000),
            (exactRationalLiteral (-264612654367364779) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-3540127422026992042379) 9830400000000000000000),
            (exactRationalLiteral (25087956473363247039) 102400000000000000000),
            (exactRationalLiteral (-367323876571295651) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3694090584558137479379) 4915200000000000000000),
            (exactRationalLiteral (-24651357306995285351) 51200000000000000000),
            (exactRationalLiteral (63567214201641583) 320000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-3540127422026992042379) 9830400000000000000000),
            (exactRationalLiteral (25087956473363247039) 102400000000000000000),
            (exactRationalLiteral (-367323876571295651) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-15674091535099337107) 9830400000000000000000),
            (exactRationalLiteral (4023979463881727111) 102400000000000000000),
            (exactRationalLiteral (-264612654367364779) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (9182846495563963369) 98304000000000000000),
            (exactRationalLiteral (-11653106390794197453) 25600000000000000000),
            (exactRationalLiteral (502538374116460393) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-1381791878409629562573) 3276800000000000000000),
            (exactRationalLiteral (103483440533342832043) 102400000000000000000),
            (exactRationalLiteral (-3890827945410622047) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (791598306545187082411) 2457600000000000000000),
            (exactRationalLiteral (-18840091031448102703) 25600000000000000000),
            (exactRationalLiteral (744200294840255203) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (186604322062980753109) 4915200000000000000000),
            (exactRationalLiteral (4784572013613055263) 51200000000000000000),
            (exactRationalLiteral (-374829436793389763) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-261035396161185036187) 9830400000000000000000),
            (exactRationalLiteral (3114026718005677103) 102400000000000000000),
            (exactRationalLiteral (-24404435610131059) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-40967607353082408221) 4915200000000000000000),
            (exactRationalLiteral (423148050494562057) 51200000000000000000),
            (exactRationalLiteral (-1887070995960773) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2211363509849170961) 4915200000000000000000),
            (exactRationalLiteral (208884021002298883) 51200000000000000000),
            (exactRationalLiteral (-151246519209607) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20541286659462148853) 4915200000000000000000),
            (exactRationalLiteral (19262725179119921) 51200000000000000000),
            (exactRationalLiteral (-1673856637216829) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2285045245172139579) 204800000000000000000),
            (exactRationalLiteral (-18508129082475463) 6400000000000000000),
            (exactRationalLiteral (-124824571779057) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (8287232503355826953) 4915200000000000000000),
            (exactRationalLiteral (93069631559222667) 51200000000000000000),
            (exactRationalLiteral (242999588099057) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (24267934167749168747) 9830400000000000000000),
            (exactRationalLiteral (70848392515968513) 102400000000000000000),
            (exactRationalLiteral (1331876355308099) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5876555468635054787) 9830400000000000000000),
            (exactRationalLiteral (82987860981832553) 102400000000000000000),
            (exactRationalLiteral (-1581439582435429) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-13807620988879074259) 9830400000000000000000),
            (exactRationalLiteral (-187493104216888121) 102400000000000000000),
            (exactRationalLiteral (4512836098055957) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (86321540523933301) 65536000000000000000),
            (exactRationalLiteral (233360881074461973) 51200000000000000000),
            (exactRationalLiteral (-11500968308722689) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5216612037556761391) 409600000000000000000),
            (exactRationalLiteral (-336703733838993231) 12800000000000000000),
            (exactRationalLiteral (9800608833077019) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (82939526215248523933) 2457600000000000000000),
            (exactRationalLiteral (2995971171237437703) 25600000000000000000),
            (exactRationalLiteral (-10036287823259483) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (36889356906599386541) 3276800000000000000000),
            (exactRationalLiteral (-19467790401937545579) 102400000000000000000),
            (exactRationalLiteral (-220321908919583169) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-164277403062153415697) 2457600000000000000000),
            (exactRationalLiteral (2818453812445494597) 25600000000000000000),
            (exactRationalLiteral (102259577997136183) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (60857443417500257209) 1966080000000000000000),
            (exactRationalLiteral (-31199915306052649) 102400000000000000000),
            (exactRationalLiteral (-271319338144522363) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (941600568448350657) 327680000000000000000),
            (exactRationalLiteral (-134514366921192951) 10240000000000000000),
            (exactRationalLiteral (6405446043866331) 320000000000000000),
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
          (exactRationalLiteral (135327756895017247) 40960000000000000000),
          (exactRationalLiteral (19037987723406189469) 614400000000000000000),
          (exactRationalLiteral (21551872917573007843) 307200000000000000000),
          (exactRationalLiteral (7014744309848025747) 409600000000000000000),
          (exactRationalLiteral (1435735189922285921) 38400000000000000000),
          (exactRationalLiteral (259819122857184283) 19200000000000000000),
          (exactRationalLiteral (111524423900127287) 76800000000000000000),
          (exactRationalLiteral (44861000900394887) 30720000000000000000),
          (exactRationalLiteral (95631455034514523) 153600000000000000000),
          (exactRationalLiteral (127524268264281257) 51200000000000000000),
          (exactRationalLiteral (133861196688200701) 76800000000000000000),
          (exactRationalLiteral (33745250197601) 3000000000000000),
          (exactRationalLiteral (858499207564632801) 204800000000000000000),
          (exactRationalLiteral (2955858349749347) 5120000000000000000),
          (exactRationalLiteral (1760114363052291537) 204800000000000000000),
          (exactRationalLiteral (33806181489727570661) 1228800000000000000000),
          (exactRationalLiteral (208180938263615139) 5120000000000000000),
          (exactRationalLiteral (106298114291677002269) 307200000000000000000),
          (exactRationalLiteral (558458690433157784297) 1228800000000000000000),
          (exactRationalLiteral (33257610327290270039) 307200000000000000000),
          (exactRationalLiteral (3569169297905956429) 1228800000000000000000),
          (exactRationalLiteral (150687665269897399639) 409600000000000000000),
          (exactRationalLiteral (471125808568243707389) 614400000000000000000),
          (exactRationalLiteral (150687665269897399639) 409600000000000000000),
          (exactRationalLiteral (3569169297905956429) 1228800000000000000000),
          (exactRationalLiteral (33257610327290270039) 307200000000000000000),
          (exactRationalLiteral (558458690433157784297) 1228800000000000000000),
          (exactRationalLiteral (106298114291677002269) 307200000000000000000),
          (exactRationalLiteral (208180938263615139) 5120000000000000000),
          (exactRationalLiteral (33806181489727570661) 1228800000000000000000),
          (exactRationalLiteral (1760114363052291537) 204800000000000000000),
          (exactRationalLiteral (2955858349749347) 5120000000000000000),
          (exactRationalLiteral (858499207564632801) 204800000000000000000),
          (exactRationalLiteral (33745250197601) 3000000000000000),
          (exactRationalLiteral (133861196688200701) 76800000000000000000),
          (exactRationalLiteral (127524268264281257) 51200000000000000000),
          (exactRationalLiteral (95631455034514523) 153600000000000000000),
          (exactRationalLiteral (44861000900394887) 30720000000000000000),
          (exactRationalLiteral (111524423900127287) 76800000000000000000),
          (exactRationalLiteral (259819122857184283) 19200000000000000000),
          (exactRationalLiteral (1435735189922285921) 38400000000000000000),
          (exactRationalLiteral (7014744309848025747) 409600000000000000000),
          (exactRationalLiteral (21551872917573007843) 307200000000000000000),
          (exactRationalLiteral (19037987723406189469) 614400000000000000000),
          (exactRationalLiteral (135327756895017247) 40960000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 10),
      (28, 26)
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
            (exactRationalLiteral (697380228807605783) 327680000000000000000),
            (exactRationalLiteral (-110112667706464071) 10240000000000000000),
            (exactRationalLiteral (5795403563498109) 320000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (300988723406308065371) 9830400000000000000000),
            (exactRationalLiteral (-1044208333695460313) 102400000000000000000),
            (exactRationalLiteral (-235184871050181469) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-146227584650830239479) 2457600000000000000000),
            (exactRationalLiteral (3183482424776326549) 25600000000000000000),
            (exactRationalLiteral (80254728168279793) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-2776544166288893493) 3276800000000000000000),
            (exactRationalLiteral (-4024525397523632511) 20480000000000000000),
            (exactRationalLiteral (-107096383920725319) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (33570896035025319721) 819200000000000000000),
            (exactRationalLiteral (116588447123414447) 1024000000000000000),
            (exactRationalLiteral (-30593708752778781) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-3507095642216281951) 245760000000000000000),
            (exactRationalLiteral (-289014799193730367) 12800000000000000000),
            (exactRationalLiteral (14043858489554413) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (7719212022164544673) 4915200000000000000000),
            (exactRationalLiteral (178828415903294981) 51200000000000000000),
            (exactRationalLiteral (-15765264276860807) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-14870093540130076213) 9830400000000000000000),
            (exactRationalLiteral (-165275739387836649) 102400000000000000000),
            (exactRationalLiteral (6595846316469779) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (6352612474542291461) 9830400000000000000000),
            (exactRationalLiteral (75215660154824089) 102400000000000000000),
            (exactRationalLiteral (-2304660831068803) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (24710483298140699101) 9830400000000000000000),
            (exactRationalLiteral (76914027453211953) 102400000000000000000),
            (exactRationalLiteral (1700941113313621) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2949378605914924517) 1638400000000000000000),
            (exactRationalLiteral (93826394899829851) 51200000000000000000),
            (exactRationalLiteral (27076416440907) 320000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6967623556788640223) 614400000000000000000),
            (exactRationalLiteral (-18978003327601703) 6400000000000000000),
            (exactRationalLiteral (-110112550784063) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-6815573324971268769) 1638400000000000000000),
            (exactRationalLiteral (12105605190365089) 51200000000000000000),
            (exactRationalLiteral (-1904703357160587) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3463350137319923623) 4915200000000000000000),
            (exactRationalLiteral (208527764769197779) 51200000000000000000),
            (exactRationalLiteral (-5376319468189) 320000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-12817035978819467913) 1638400000000000000000),
            (exactRationalLiteral (415727749314799673) 51200000000000000000),
            (exactRationalLiteral (-1823079593920419) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-242653990714167709357) 9830400000000000000000),
            (exactRationalLiteral (3011458158717571327) 102400000000000000000),
            (exactRationalLiteral (-26879844033921829) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (210975008420184678179) 4915200000000000000000),
            (exactRationalLiteral (673171604992526307) 10240000000000000000),
            (exactRationalLiteral (-334527557531822101) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (137443658683934126489) 491520000000000000000),
            (exactRationalLiteral (-15998225089542529983) 25600000000000000000),
            (exactRationalLiteral (676732676112531157) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-3569796264972853364929) 9830400000000000000000),
            (exactRationalLiteral (88604459952153241403) 102400000000000000000),
            (exactRationalLiteral (-3548662345184173273) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (165500697057802603831) 2457600000000000000000),
            (exactRationalLiteral (-9734096632292766077) 25600000000000000000),
            (exactRationalLiteral (91393301026851059) 160000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (5402325342990957451) 9830400000000000000000),
            (exactRationalLiteral (603894964003284523) 20480000000000000000),
            (exactRationalLiteral (-237639667565287469) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-1131307314166577580287) 3276800000000000000000),
            (exactRationalLiteral (23661474570045747983) 102400000000000000000),
            (exactRationalLiteral (-345917075087453877) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (3549930042737850662773) 4915200000000000000000),
            (exactRationalLiteral (-23413228438169253431) 51200000000000000000),
            (exactRationalLiteral (60245672680961609) 320000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-1131307314166577580287) 3276800000000000000000),
            (exactRationalLiteral (23661474570045747983) 102400000000000000000),
            (exactRationalLiteral (-345917075087453877) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (5402325342990957451) 9830400000000000000000),
            (exactRationalLiteral (603894964003284523) 20480000000000000000),
            (exactRationalLiteral (-237639667565287469) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (165500697057802603831) 2457600000000000000000),
            (exactRationalLiteral (-9734096632292766077) 25600000000000000000),
            (exactRationalLiteral (91393301026851059) 160000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-3569796264972853364929) 9830400000000000000000),
            (exactRationalLiteral (88604459952153241403) 102400000000000000000),
            (exactRationalLiteral (-3548662345184173273) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (137443658683934126489) 491520000000000000000),
            (exactRationalLiteral (-15998225089542529983) 25600000000000000000),
            (exactRationalLiteral (676732676112531157) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (210975008420184678179) 4915200000000000000000),
            (exactRationalLiteral (673171604992526307) 10240000000000000000),
            (exactRationalLiteral (-334527557531822101) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-242653990714167709357) 9830400000000000000000),
            (exactRationalLiteral (3011458158717571327) 102400000000000000000),
            (exactRationalLiteral (-26879844033921829) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-12817035978819467913) 1638400000000000000000),
            (exactRationalLiteral (415727749314799673) 51200000000000000000),
            (exactRationalLiteral (-1823079593920419) 1600000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3463350137319923623) 4915200000000000000000),
            (exactRationalLiteral (208527764769197779) 51200000000000000000),
            (exactRationalLiteral (-5376319468189) 320000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6815573324971268769) 1638400000000000000000),
            (exactRationalLiteral (12105605190365089) 51200000000000000000),
            (exactRationalLiteral (-1904703357160587) 1600000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6967623556788640223) 614400000000000000000),
            (exactRationalLiteral (-18978003327601703) 6400000000000000000),
            (exactRationalLiteral (-110112550784063) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (2949378605914924517) 1638400000000000000000),
            (exactRationalLiteral (93826394899829851) 51200000000000000000),
            (exactRationalLiteral (27076416440907) 320000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (24710483298140699101) 9830400000000000000000),
            (exactRationalLiteral (76914027453211953) 102400000000000000000),
            (exactRationalLiteral (1700941113313621) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6352612474542291461) 9830400000000000000000),
            (exactRationalLiteral (75215660154824089) 102400000000000000000),
            (exactRationalLiteral (-2304660831068803) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-14870093540130076213) 9830400000000000000000),
            (exactRationalLiteral (-165275739387836649) 102400000000000000000),
            (exactRationalLiteral (6595846316469779) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (7719212022164544673) 4915200000000000000000),
            (exactRationalLiteral (178828415903294981) 51200000000000000000),
            (exactRationalLiteral (-15765264276860807) 1600000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-3507095642216281951) 245760000000000000000),
            (exactRationalLiteral (-289014799193730367) 12800000000000000000),
            (exactRationalLiteral (14043858489554413) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (33570896035025319721) 819200000000000000000),
            (exactRationalLiteral (116588447123414447) 1024000000000000000),
            (exactRationalLiteral (-30593708752778781) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2776544166288893493) 3276800000000000000000),
            (exactRationalLiteral (-4024525397523632511) 20480000000000000000),
            (exactRationalLiteral (-107096383920725319) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-146227584650830239479) 2457600000000000000000),
            (exactRationalLiteral (3183482424776326549) 25600000000000000000),
            (exactRationalLiteral (80254728168279793) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (300988723406308065371) 9830400000000000000000),
            (exactRationalLiteral (-1044208333695460313) 102400000000000000000),
            (exactRationalLiteral (-235184871050181469) 3200000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (697380228807605783) 327680000000000000000),
            (exactRationalLiteral (-110112667706464071) 10240000000000000000),
            (exactRationalLiteral (5795403563498109) 320000000000000000),
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
          (exactRationalLiteral (101673746728037) 40960000000000000),
          (exactRationalLiteral (4740589477510886429) 153600000000000000000),
          (exactRationalLiteral (2430097895558436743) 38400000000000000000),
          (exactRationalLiteral (2873424577124329799) 409600000000000000000),
          (exactRationalLiteral (13669345225326118337) 307200000000000000000),
          (exactRationalLiteral (152985578403047491) 10240000000000000000),
          (exactRationalLiteral (341927888710824089) 204800000000000000000),
          (exactRationalLiteral (1918136464279371239) 1228800000000000000000),
          (exactRationalLiteral (821372982736155079) 1228800000000000000000),
          (exactRationalLiteral (3118314092027409823) 1228800000000000000000),
          (exactRationalLiteral (1141245917492241181) 614400000000000000000),
          (exactRationalLiteral (292703356183887501) 25600000000000000000),
          (exactRationalLiteral (320134929331193929) 76800000000000000000),
          (exactRationalLiteral (511114371162053557) 614400000000000000000),
          (exactRationalLiteral (620371756545087253) 76800000000000000000),
          (exactRationalLiteral (786774271931907167) 30720000000000000000),
          (exactRationalLiteral (27511143845263486289) 614400000000000000000),
          (exactRationalLiteral (11519951570718744967) 38400000000000000000),
          (exactRationalLiteral (60100417416640294271) 153600000000000000000),
          (exactRationalLiteral (3064010506321480789) 38400000000000000000),
          (exactRationalLiteral (1720164661718175193) 1228800000000000000000),
          (exactRationalLiteral (54155544075560535427) 153600000000000000000),
          (exactRationalLiteral (18859800609356117433) 25600000000000000000),
          (exactRationalLiteral (54155544075560535427) 153600000000000000000),
          (exactRationalLiteral (1720164661718175193) 1228800000000000000000),
          (exactRationalLiteral (3064010506321480789) 38400000000000000000),
          (exactRationalLiteral (60100417416640294271) 153600000000000000000),
          (exactRationalLiteral (11519951570718744967) 38400000000000000000),
          (exactRationalLiteral (27511143845263486289) 614400000000000000000),
          (exactRationalLiteral (786774271931907167) 30720000000000000000),
          (exactRationalLiteral (620371756545087253) 76800000000000000000),
          (exactRationalLiteral (511114371162053557) 614400000000000000000),
          (exactRationalLiteral (320134929331193929) 76800000000000000000),
          (exactRationalLiteral (292703356183887501) 25600000000000000000),
          (exactRationalLiteral (1141245917492241181) 614400000000000000000),
          (exactRationalLiteral (3118314092027409823) 1228800000000000000000),
          (exactRationalLiteral (821372982736155079) 1228800000000000000000),
          (exactRationalLiteral (1918136464279371239) 1228800000000000000000),
          (exactRationalLiteral (341927888710824089) 204800000000000000000),
          (exactRationalLiteral (152985578403047491) 10240000000000000000),
          (exactRationalLiteral (13669345225326118337) 307200000000000000000),
          (exactRationalLiteral (2873424577124329799) 409600000000000000000),
          (exactRationalLiteral (2430097895558436743) 38400000000000000000),
          (exactRationalLiteral (4740589477510886429) 153600000000000000000),
          (exactRationalLiteral (101673746728037) 40960000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 9),
      (28, 25)
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
            (exactRationalLiteral (499523117674845781) 327680000000000000000),
            (exactRationalLiteral (-88151138413208079) 10240000000000000000),
            (exactRationalLiteral (5185361083129887) 320000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (292045792819910489441) 9830400000000000000000),
            (exactRationalLiteral (-1912678883707504401) 102400000000000000000),
            (exactRationalLiteral (-7962016158233623) 128000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-126251652763468348229) 2457600000000000000000),
            (exactRationalLiteral (3460491637791732941) 25600000000000000000),
            (exactRationalLiteral (58249878339423403) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-43299216310542976079) 3276800000000000000000),
            (exactRationalLiteral (-20324561473303348131) 102400000000000000000),
            (exactRationalLiteral (6129141078132531) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (117751600984836703649) 2457600000000000000000),
            (exactRationalLiteral (550244300243041491) 5120000000000000000),
            (exactRationalLiteral (-51151129682298079) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-763362708229729177) 49152000000000000000),
            (exactRationalLiteral (-224352865922557927) 12800000000000000000),
            (exactRationalLiteral (18287108146031807) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (8585942162389432403) 4915200000000000000000),
            (exactRationalLiteral (107238766859575517) 51200000000000000000),
            (exactRationalLiteral (-801182409799957) 64000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-15774265779785803471) 9830400000000000000000),
            (exactRationalLiteral (-134726333685129889) 102400000000000000000),
            (exactRationalLiteral (8678856534883601) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (6773357620503876863) 9830400000000000000000),
            (exactRationalLiteral (64550574333282129) 102400000000000000000),
            (exactRationalLiteral (-3027882079702177) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (8397951671750585453) 3276800000000000000000),
            (exactRationalLiteral (84455921422477481) 102400000000000000000),
            (exactRationalLiteral (2070005871319143) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (9412288302106628989) 4915200000000000000000),
            (exactRationalLiteral (94152688216858947) 51200000000000000000),
            (exactRationalLiteral (27764576310013) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7082754079279679221) 614400000000000000000),
            (exactRationalLiteral (-19389029488747967) 6400000000000000000),
            (exactRationalLiteral (-95400529789069) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-20397866170937317849) 4915200000000000000000),
            (exactRationalLiteral (161003932873409) 2048000000000000000),
            (exactRationalLiteral (-427110015420869) 320000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (314312773763632907) 327680000000000000000),
            (exactRationalLiteral (208668968223571323) 51200000000000000000),
            (exactRationalLiteral (97483324527717) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-35978362430088489313) 4915200000000000000000),
            (exactRationalLiteral (81712682748639741) 10240000000000000000),
            (exactRationalLiteral (-351817638376013) 320000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-224917701523964506423) 9830400000000000000000),
            (exactRationalLiteral (2898987965734302471) 102400000000000000000),
            (exactRationalLiteral (-29355252457712599) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (3030893778621664971) 65536000000000000000),
            (exactRationalLiteral (421670310671695691) 10240000000000000000),
            (exactRationalLiteral (-294225678270254439) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (599079864520854930247) 2457600000000000000000),
            (exactRationalLiteral (-13426229622547853447) 25600000000000000000),
            (exactRationalLiteral (609265057384807111) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-3079384791001238200691) 9830400000000000000000),
            (exactRationalLiteral (75094141771869445859) 102400000000000000000),
            (exactRationalLiteral (-3206496744957724499) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (112397427849728250517) 2457600000000000000000),
            (exactRationalLiteral (-7997374349720155093) 25600000000000000000),
            (exactRationalLiteral (411394636152050197) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (6925130066504784251) 3276800000000000000000),
            (exactRationalLiteral (2122862123359427359) 102400000000000000000),
            (exactRationalLiteral (-210666680763210159) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-3256018472774572332391) 9830400000000000000000),
            (exactRationalLiteral (22320619872663616023) 102400000000000000000),
            (exactRationalLiteral (-324510273603612103) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1137666327213093079749) 1638400000000000000000),
            (exactRationalLiteral (-22241530399756820991) 51200000000000000000),
            (exactRationalLiteral (11384826232056327) 64000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-3256018472774572332391) 9830400000000000000000),
            (exactRationalLiteral (22320619872663616023) 102400000000000000000),
            (exactRationalLiteral (-324510273603612103) 3200000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6925130066504784251) 3276800000000000000000),
            (exactRationalLiteral (2122862123359427359) 102400000000000000000),
            (exactRationalLiteral (-210666680763210159) 3200000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (112397427849728250517) 2457600000000000000000),
            (exactRationalLiteral (-7997374349720155093) 25600000000000000000),
            (exactRationalLiteral (411394636152050197) 800000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-3079384791001238200691) 9830400000000000000000),
            (exactRationalLiteral (75094141771869445859) 102400000000000000000),
            (exactRationalLiteral (-3206496744957724499) 3200000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (599079864520854930247) 2457600000000000000000),
            (exactRationalLiteral (-13426229622547853447) 25600000000000000000),
            (exactRationalLiteral (609265057384807111) 800000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (3030893778621664971) 65536000000000000000),
            (exactRationalLiteral (421670310671695691) 10240000000000000000),
            (exactRationalLiteral (-294225678270254439) 1600000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-224917701523964506423) 9830400000000000000000),
            (exactRationalLiteral (2898987965734302471) 102400000000000000000),
            (exactRationalLiteral (-29355252457712599) 3200000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-35978362430088489313) 4915200000000000000000),
            (exactRationalLiteral (81712682748639741) 10240000000000000000),
            (exactRationalLiteral (-351817638376013) 320000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (314312773763632907) 327680000000000000000),
            (exactRationalLiteral (208668968223571323) 51200000000000000000),
            (exactRationalLiteral (97483324527717) 1600000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-20397866170937317849) 4915200000000000000000),
            (exactRationalLiteral (161003932873409) 2048000000000000000),
            (exactRationalLiteral (-427110015420869) 320000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-7082754079279679221) 614400000000000000000),
            (exactRationalLiteral (-19389029488747967) 6400000000000000000),
            (exactRationalLiteral (-95400529789069) 200000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (9412288302106628989) 4915200000000000000000),
            (exactRationalLiteral (94152688216858947) 51200000000000000000),
            (exactRationalLiteral (27764576310013) 1600000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (8397951671750585453) 3276800000000000000000),
            (exactRationalLiteral (84455921422477481) 102400000000000000000),
            (exactRationalLiteral (2070005871319143) 3200000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6773357620503876863) 9830400000000000000000),
            (exactRationalLiteral (64550574333282129) 102400000000000000000),
            (exactRationalLiteral (-3027882079702177) 3200000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-15774265779785803471) 9830400000000000000000),
            (exactRationalLiteral (-134726333685129889) 102400000000000000000),
            (exactRationalLiteral (8678856534883601) 3200000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (8585942162389432403) 4915200000000000000000),
            (exactRationalLiteral (107238766859575517) 51200000000000000000),
            (exactRationalLiteral (-801182409799957) 64000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-763362708229729177) 49152000000000000000),
            (exactRationalLiteral (-224352865922557927) 12800000000000000000),
            (exactRationalLiteral (18287108146031807) 400000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (117751600984836703649) 2457600000000000000000),
            (exactRationalLiteral (550244300243041491) 5120000000000000000),
            (exactRationalLiteral (-51151129682298079) 800000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-43299216310542976079) 3276800000000000000000),
            (exactRationalLiteral (-20324561473303348131) 102400000000000000000),
            (exactRationalLiteral (6129141078132531) 3200000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-126251652763468348229) 2457600000000000000000),
            (exactRationalLiteral (3460491637791732941) 25600000000000000000),
            (exactRationalLiteral (58249878339423403) 800000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (292045792819910489441) 9830400000000000000000),
            (exactRationalLiteral (-1912678883707504401) 102400000000000000000),
            (exactRationalLiteral (-7962016158233623) 128000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (499523117674845781) 327680000000000000000),
            (exactRationalLiteral (-88151138413208079) 10240000000000000000),
            (exactRationalLiteral (5185361083129887) 320000000000000000),
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
          (exactRationalLiteral (74120161364738973) 40960000000000000000),
          (exactRationalLiteral (37146076378202288809) 1228800000000000000000),
          (exactRationalLiteral (17055921952113856081) 307200000000000000000),
          (exactRationalLiteral (15527045342269299) 800000000000000000),
          (exactRationalLiteral (2560252551045139) 50000000000000000),
          (exactRationalLiteral (9619210622189731) 600000000000000000),
          (exactRationalLiteral (431906134484819) 240000000000000000),
          (exactRationalLiteral (3943204762238119) 2400000000000000000),
          (exactRationalLiteral (1698624044589917) 2400000000000000000),
          (exactRationalLiteral (6214262043337927) 2400000000000000000),
          (exactRationalLiteral (98620359819877) 50000000000000000),
          (exactRationalLiteral (6973828138012493) 600000000000000000),
          (exactRationalLiteral (510405817319354117) 122880000000000000000),
          (exactRationalLiteral (651984026313443) 600000000000000000),
          (exactRationalLiteral (186046809657973729) 24576000000000000000),
          (exactRationalLiteral (29212686684291082031) 1228800000000000000000),
          (exactRationalLiteral (56830947744511799) 1200000000000000000),
          (exactRationalLiteral (80152510296252096743) 307200000000000000000),
          (exactRationalLiteral (138102407889659705673) 409600000000000000000),
          (exactRationalLiteral (17205815092729496117) 307200000000000000000),
          (exactRationalLiteral (6475943120289073) 2400000000000000000),
          (exactRationalLiteral (415495570826764492207) 1228800000000000000000),
          (exactRationalLiteral (87014643466493890667) 122880000000000000000),
          (exactRationalLiteral (415495570826764492207) 1228800000000000000000),
          (exactRationalLiteral (6475943120289073) 2400000000000000000),
          (exactRationalLiteral (17205815092729496117) 307200000000000000000),
          (exactRationalLiteral (138102407889659705673) 409600000000000000000),
          (exactRationalLiteral (80152510296252096743) 307200000000000000000),
          (exactRationalLiteral (56830947744511799) 1200000000000000000),
          (exactRationalLiteral (29212686684291082031) 1228800000000000000000),
          (exactRationalLiteral (186046809657973729) 24576000000000000000),
          (exactRationalLiteral (651984026313443) 600000000000000000),
          (exactRationalLiteral (510405817319354117) 122880000000000000000),
          (exactRationalLiteral (6973828138012493) 600000000000000000),
          (exactRationalLiteral (98620359819877) 50000000000000000),
          (exactRationalLiteral (6214262043337927) 2400000000000000000),
          (exactRationalLiteral (1698624044589917) 2400000000000000000),
          (exactRationalLiteral (3943204762238119) 2400000000000000000),
          (exactRationalLiteral (431906134484819) 240000000000000000),
          (exactRationalLiteral (9619210622189731) 600000000000000000),
          (exactRationalLiteral (2560252551045139) 50000000000000000),
          (exactRationalLiteral (15527045342269299) 800000000000000000),
          (exactRationalLiteral (17055921952113856081) 307200000000000000000),
          (exactRationalLiteral (37146076378202288809) 1228800000000000000000),
          (exactRationalLiteral (74120161364738973) 40960000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (28, 8),
      (28, 24)
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
theorem generatorCoordinates23_valid : ∀ i, (generatorCoordinates23 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
