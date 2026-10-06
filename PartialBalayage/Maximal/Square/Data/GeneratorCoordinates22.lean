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

/-- Actual coordinate interval candidates, block 22. -/
def generatorCoordinates22 : Fin 8 → GeneratorCoordinateData := ![
  {
    cubic :=
      {
        cell := 5
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
            (exactRationalLiteral (2745191161656999) 5120000000000000000),
            (exactRationalLiteral (-2745191161656999) 640000000000000000),
            (exactRationalLiteral (915063720552333) 80000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (3916956772828221659) 153600000000000000000),
            (exactRationalLiteral (-215718880286665561) 6400000000000000000),
            (exactRationalLiteral (-5435711810999417) 160000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1114856881803736301) 38400000000000000000),
            (exactRationalLiteral (235495612395328881) 1600000000000000000),
            (exactRationalLiteral (809438441820607) 200000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-2225155156968180181) 51200000000000000000),
            (exactRationalLiteral (-1177996937502268731) 6400000000000000000),
            (exactRationalLiteral (72298238393819289) 800000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (2404667968262460991) 38400000000000000000),
            (exactRationalLiteral (24784280534665443) 320000000000000000),
            (exactRationalLiteral (-25636170501524081) 200000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-21679817166770183) 1280000000000000000),
            (exactRationalLiteral (722427265232973) 800000000000000000),
            (exactRationalLiteral (7223808071806323) 100000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (43884313275518299) 25600000000000000000),
            (exactRationalLiteral (-9147533449508763) 3200000000000000000),
            (exactRationalLiteral (-1534515008267211) 80000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-265844662598369029) 153600000000000000000),
            (exactRationalLiteral (-1368758787882569) 6400000000000000000),
            (exactRationalLiteral (3471595520229539) 800000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (116708183616966557) 153600000000000000000),
            (exactRationalLiteral (1576967995521449) 6400000000000000000),
            (exactRationalLiteral (-1208983800321403) 800000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (416234544129893741) 153600000000000000000),
            (exactRationalLiteral (6860580600671121) 6400000000000000000),
            (exactRationalLiteral (748166941583237) 800000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (169061482413505571) 76800000000000000000),
            (exactRationalLiteral (5817819697267347) 3200000000000000000),
            (exactRationalLiteral (-60319797106573) 400000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-19218294427168989) 1600000000000000000),
            (exactRationalLiteral (-1259945907762577) 400000000000000000),
            (exactRationalLiteral (-3663779831349) 12500000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-320501310498267191) 76800000000000000000),
            (exactRationalLiteral (-50539966121263) 128000000000000000),
            (exactRationalLiteral (-135633343848187) 80000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (4912381366727771) 3072000000000000000),
            (exactRationalLiteral (13199897687012923) 3200000000000000000),
            (exactRationalLiteral (102098907299843) 400000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-468403802745374867) 76800000000000000000),
            (exactRationalLiteral (4897155304373781) 640000000000000000),
            (exactRationalLiteral (-79955484338959) 80000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2871706859355708397) 153600000000000000000),
            (exactRationalLiteral (160905802241236991) 6400000000000000000),
            (exactRationalLiteral (-8885943379297381) 800000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (149621405175363091) 3072000000000000000),
            (exactRationalLiteral (-4126646732180877) 640000000000000000),
            (exactRationalLiteral (-48367745029083821) 400000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (6861946458062732953) 38400000000000000000),
            (exactRationalLiteral (-511057767674770807) 1600000000000000000),
            (exactRationalLiteral (110149002641374249) 200000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-11312888386879545843) 51200000000000000000),
            (exactRationalLiteral (2956640270320175659) 6400000000000000000),
            (exactRationalLiteral (-587770686097900641) 800000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (319424507874091723) 38400000000000000000),
            (exactRationalLiteral (-278317271904826053) 1600000000000000000),
            (exactRationalLiteral (74366240924134363) 200000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (601627072934294267) 153600000000000000000),
            (exactRationalLiteral (22084853172080759) 6400000000000000000),
            (exactRationalLiteral (-35808553439504221) 800000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-46003273751752326389) 153600000000000000000),
            (exactRationalLiteral (1208943884698469823) 6400000000000000000),
            (exactRationalLiteral (-67748317473501917) 800000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (48432571767231563213) 76800000000000000000),
            (exactRationalLiteral (-1225182511674077351) 3200000000000000000),
            (exactRationalLiteral (486202773585817) 3200000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-46003273751752326389) 153600000000000000000),
            (exactRationalLiteral (1208943884698469823) 6400000000000000000),
            (exactRationalLiteral (-67748317473501917) 800000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (601627072934294267) 153600000000000000000),
            (exactRationalLiteral (22084853172080759) 6400000000000000000),
            (exactRationalLiteral (-35808553439504221) 800000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (319424507874091723) 38400000000000000000),
            (exactRationalLiteral (-278317271904826053) 1600000000000000000),
            (exactRationalLiteral (74366240924134363) 200000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-11312888386879545843) 51200000000000000000),
            (exactRationalLiteral (2956640270320175659) 6400000000000000000),
            (exactRationalLiteral (-587770686097900641) 800000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6861946458062732953) 38400000000000000000),
            (exactRationalLiteral (-511057767674770807) 1600000000000000000),
            (exactRationalLiteral (110149002641374249) 200000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (149621405175363091) 3072000000000000000),
            (exactRationalLiteral (-4126646732180877) 640000000000000000),
            (exactRationalLiteral (-48367745029083821) 400000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2871706859355708397) 153600000000000000000),
            (exactRationalLiteral (160905802241236991) 6400000000000000000),
            (exactRationalLiteral (-8885943379297381) 800000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-468403802745374867) 76800000000000000000),
            (exactRationalLiteral (4897155304373781) 640000000000000000),
            (exactRationalLiteral (-79955484338959) 80000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (4912381366727771) 3072000000000000000),
            (exactRationalLiteral (13199897687012923) 3200000000000000000),
            (exactRationalLiteral (102098907299843) 400000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-320501310498267191) 76800000000000000000),
            (exactRationalLiteral (-50539966121263) 128000000000000000),
            (exactRationalLiteral (-135633343848187) 80000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-19218294427168989) 1600000000000000000),
            (exactRationalLiteral (-1259945907762577) 400000000000000000),
            (exactRationalLiteral (-3663779831349) 12500000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (169061482413505571) 76800000000000000000),
            (exactRationalLiteral (5817819697267347) 3200000000000000000),
            (exactRationalLiteral (-60319797106573) 400000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (416234544129893741) 153600000000000000000),
            (exactRationalLiteral (6860580600671121) 6400000000000000000),
            (exactRationalLiteral (748166941583237) 800000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (116708183616966557) 153600000000000000000),
            (exactRationalLiteral (1576967995521449) 6400000000000000000),
            (exactRationalLiteral (-1208983800321403) 800000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-265844662598369029) 153600000000000000000),
            (exactRationalLiteral (-1368758787882569) 6400000000000000000),
            (exactRationalLiteral (3471595520229539) 800000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (43884313275518299) 25600000000000000000),
            (exactRationalLiteral (-9147533449508763) 3200000000000000000),
            (exactRationalLiteral (-1534515008267211) 80000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-21679817166770183) 1280000000000000000),
            (exactRationalLiteral (722427265232973) 800000000000000000),
            (exactRationalLiteral (7223808071806323) 100000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (2404667968262460991) 38400000000000000000),
            (exactRationalLiteral (24784280534665443) 320000000000000000),
            (exactRationalLiteral (-25636170501524081) 200000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2225155156968180181) 51200000000000000000),
            (exactRationalLiteral (-1177996937502268731) 6400000000000000000),
            (exactRationalLiteral (72298238393819289) 800000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-1114856881803736301) 38400000000000000000),
            (exactRationalLiteral (235495612395328881) 1600000000000000000),
            (exactRationalLiteral (809438441820607) 200000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (3916956772828221659) 153600000000000000000),
            (exactRationalLiteral (-215718880286665561) 6400000000000000000),
            (exactRationalLiteral (-5435711810999417) 160000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2745191161656999) 5120000000000000000),
            (exactRationalLiteral (-2745191161656999) 640000000000000000),
            (exactRationalLiteral (915063720552333) 80000000000000000),
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
          (exactRationalLiteral (413997866905435831) 6400000000000000000),
          (exactRationalLiteral (336155619289138843) 4800000000000000000),
          (exactRationalLiteral (41727532892045599) 2400000000000000000),
          (exactRationalLiteral (4573153135416583) 2400000000000000000),
          (exactRationalLiteral (16982907625980503) 9600000000000000000),
          (exactRationalLiteral (7490984127320381) 9600000000000000000),
          (exactRationalLiteral (18301888297319149) 6400000000000000000),
          (exactRationalLiteral (23285021670130079) 9600000000000000000),
          (exactRationalLiteral (29781553408445089) 2400000000000000000),
          (exactRationalLiteral (1632208657375283) 384000000000000000),
          (exactRationalLiteral (6782404433836121) 3200000000000000000),
          (exactRationalLiteral (2828606563943157) 400000000000000000),
          (exactRationalLiteral (52810068625084627) 2400000000000000000),
          (exactRationalLiteral (119677720240776541) 2400000000000000000),
          (exactRationalLiteral (68432035768554923) 300000000000000000),
          (exactRationalLiteral (699109075468845169) 2400000000000000000),
          (exactRationalLiteral (273488472822671) 7500000000000000),
          (exactRationalLiteral (40377124134052537) 9600000000000000000),
          (exactRationalLiteral (259604446661511263) 800000000000000000),
          (exactRationalLiteral (817167956189846509) 1200000000000000000),
          (exactRationalLiteral (259604446661511263) 800000000000000000),
          (exactRationalLiteral (40377124134052537) 9600000000000000000),
          (exactRationalLiteral (273488472822671) 7500000000000000),
          (exactRationalLiteral (699109075468845169) 2400000000000000000),
          (exactRationalLiteral (68432035768554923) 300000000000000000),
          (exactRationalLiteral (119677720240776541) 2400000000000000000),
          (exactRationalLiteral (52810068625084627) 2400000000000000000),
          (exactRationalLiteral (2828606563943157) 400000000000000000),
          (exactRationalLiteral (6782404433836121) 3200000000000000000),
          (exactRationalLiteral (1632208657375283) 384000000000000000),
          (exactRationalLiteral (29781553408445089) 2400000000000000000),
          (exactRationalLiteral (23285021670130079) 9600000000000000000),
          (exactRationalLiteral (18301888297319149) 6400000000000000000),
          (exactRationalLiteral (7490984127320381) 9600000000000000000),
          (exactRationalLiteral (16982907625980503) 9600000000000000000),
          (exactRationalLiteral (4573153135416583) 2400000000000000000),
          (exactRationalLiteral (41727532892045599) 2400000000000000000),
          (exactRationalLiteral (336155619289138843) 4800000000000000000),
          (exactRationalLiteral (413997866905435831) 6400000000000000000),
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
      (42, 11),
      (42, 15),
      (42, 19),
      (42, 23)
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
            (exactRationalLiteral (101673746728037) 5120000000000000000),
            (exactRationalLiteral (-305021240184111) 640000000000000000),
            (exactRationalLiteral (305021240184111) 80000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (2441038650825626849) 153600000000000000000),
            (exactRationalLiteral (-252164182317972113) 6400000000000000000),
            (exactRationalLiteral (8955908039343809) 800000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (219810654554658709) 38400000000000000000),
            (exactRationalLiteral (194723666504898529) 1600000000000000000),
            (exactRationalLiteral (-21195411387035783) 200000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-4140988711732296687) 51200000000000000000),
            (exactRationalLiteral (-5298823471434207) 51200000000000000),
            (exactRationalLiteral (185523763392677139) 800000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (919444218188686039) 12800000000000000000),
            (exactRationalLiteral (-3947624238361541) 320000000000000000),
            (exactRationalLiteral (-46193591431043379) 200000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-43440799684513891) 3840000000000000000),
            (exactRationalLiteral (38104158865413053) 800000000000000000),
            (exactRationalLiteral (11467057728283717) 100000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-32360345239082813) 76800000000000000000),
            (exactRationalLiteral (-48366425551129219) 3200000000000000000),
            (exactRationalLiteral (-11936871009474173) 400000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-224066028209254687) 153600000000000000000),
            (exactRationalLiteral (16683643729863231) 6400000000000000000),
            (exactRationalLiteral (5554605738643361) 800000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (108769300991704919) 153600000000000000000),
            (exactRationalLiteral (-4705409703030911) 6400000000000000000),
            (exactRationalLiteral (-1932205048954777) 800000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (467852290064941399) 153600000000000000000),
            (exactRationalLiteral (10591377883015113) 6400000000000000000),
            (exactRationalLiteral (1117231699588759) 800000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (67604697669417563) 25600000000000000000),
            (exactRationalLiteral (5361305497052011) 3200000000000000000),
            (exactRationalLiteral (-33587460600219) 80000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-30746613839378543) 2400000000000000000),
            (exactRationalLiteral (-1289142343074173) 400000000000000000),
            (exactRationalLiteral (28450834799) 25000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-112381230975707631) 25600000000000000000),
            (exactRationalLiteral (-4437859469882831) 3200000000000000000),
            (exactRationalLiteral (-909013439184693) 400000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (203731566865344577) 76800000000000000000),
            (exactRationalLiteral (13857023159949619) 3200000000000000000),
            (exactRationalLiteral (45292765833701) 80000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-108676835688779187) 25600000000000000000),
            (exactRationalLiteral (23014649639170433) 3200000000000000000),
            (exactRationalLiteral (-335786019654441) 400000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2022805000155018103) 153600000000000000000),
            (exactRationalLiteral (120411211876465927) 6400000000000000000),
            (exactRationalLiteral (-11361351803088151) 800000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (3197530304115915761) 76800000000000000000),
            (exactRationalLiteral (-26700091050820869) 640000000000000000),
            (exactRationalLiteral (-8065865767516159) 400000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (969503481759940583) 7680000000000000000),
            (exactRationalLiteral (-205396994564721903) 1600000000000000000),
            (exactRationalLiteral (42681383913650203) 200000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-21883409370986596171) 153600000000000000000),
            (exactRationalLiteral (1289888726381470643) 6400000000000000000),
            (exactRationalLiteral (-245605085871451867) 800000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-640371708394072631) 38400000000000000000),
            (exactRationalLiteral (-71996046172698797) 1600000000000000000),
            (exactRationalLiteral (5758874388385853) 40000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (412325497901037409) 153600000000000000000),
            (exactRationalLiteral (-13440677396356301) 1280000000000000000),
            (exactRationalLiteral (-8835566637426911) 800000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-13158987682436054453) 51200000000000000000),
            (exactRationalLiteral (980764217772145703) 6400000000000000000),
            (exactRationalLiteral (-46341515989660143) 800000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (41744350027152225127) 76800000000000000000),
            (exactRationalLiteral (-1015296540087968591) 3200000000000000000),
            (exactRationalLiteral (8833527818965451) 80000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-13158987682436054453) 51200000000000000000),
            (exactRationalLiteral (980764217772145703) 6400000000000000000),
            (exactRationalLiteral (-46341515989660143) 800000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (412325497901037409) 153600000000000000000),
            (exactRationalLiteral (-13440677396356301) 1280000000000000000),
            (exactRationalLiteral (-8835566637426911) 800000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-640371708394072631) 38400000000000000000),
            (exactRationalLiteral (-71996046172698797) 1600000000000000000),
            (exactRationalLiteral (5758874388385853) 40000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-21883409370986596171) 153600000000000000000),
            (exactRationalLiteral (1289888726381470643) 6400000000000000000),
            (exactRationalLiteral (-245605085871451867) 800000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (969503481759940583) 7680000000000000000),
            (exactRationalLiteral (-205396994564721903) 1600000000000000000),
            (exactRationalLiteral (42681383913650203) 200000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (3197530304115915761) 76800000000000000000),
            (exactRationalLiteral (-26700091050820869) 640000000000000000),
            (exactRationalLiteral (-8065865767516159) 400000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2022805000155018103) 153600000000000000000),
            (exactRationalLiteral (120411211876465927) 6400000000000000000),
            (exactRationalLiteral (-11361351803088151) 800000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-108676835688779187) 25600000000000000000),
            (exactRationalLiteral (23014649639170433) 3200000000000000000),
            (exactRationalLiteral (-335786019654441) 400000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (203731566865344577) 76800000000000000000),
            (exactRationalLiteral (13857023159949619) 3200000000000000000),
            (exactRationalLiteral (45292765833701) 80000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-112381230975707631) 25600000000000000000),
            (exactRationalLiteral (-4437859469882831) 3200000000000000000),
            (exactRationalLiteral (-909013439184693) 400000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-30746613839378543) 2400000000000000000),
            (exactRationalLiteral (-1289142343074173) 400000000000000000),
            (exactRationalLiteral (28450834799) 25000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (67604697669417563) 25600000000000000000),
            (exactRationalLiteral (5361305497052011) 3200000000000000000),
            (exactRationalLiteral (-33587460600219) 80000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (467852290064941399) 153600000000000000000),
            (exactRationalLiteral (10591377883015113) 6400000000000000000),
            (exactRationalLiteral (1117231699588759) 800000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (108769300991704919) 153600000000000000000),
            (exactRationalLiteral (-4705409703030911) 6400000000000000000),
            (exactRationalLiteral (-1932205048954777) 800000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-224066028209254687) 153600000000000000000),
            (exactRationalLiteral (16683643729863231) 6400000000000000000),
            (exactRationalLiteral (5554605738643361) 800000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-32360345239082813) 76800000000000000000),
            (exactRationalLiteral (-48366425551129219) 3200000000000000000),
            (exactRationalLiteral (-11936871009474173) 400000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-43440799684513891) 3840000000000000000),
            (exactRationalLiteral (38104158865413053) 800000000000000000),
            (exactRationalLiteral (11467057728283717) 100000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (919444218188686039) 12800000000000000000),
            (exactRationalLiteral (-3947624238361541) 320000000000000000),
            (exactRationalLiteral (-46193591431043379) 200000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-4140988711732296687) 51200000000000000000),
            (exactRationalLiteral (-5298823471434207) 51200000000000000),
            (exactRationalLiteral (185523763392677139) 800000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (219810654554658709) 38400000000000000000),
            (exactRationalLiteral (194723666504898529) 1600000000000000000),
            (exactRationalLiteral (-21195411387035783) 200000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (2441038650825626849) 153600000000000000000),
            (exactRationalLiteral (-252164182317972113) 6400000000000000000),
            (exactRationalLiteral (8955908039343809) 800000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (101673746728037) 5120000000000000000),
            (exactRationalLiteral (-305021240184111) 640000000000000000),
            (exactRationalLiteral (305021240184111) 80000000000000000),
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
          (exactRationalLiteral (5698382773389209) 300000000000000000),
          (exactRationalLiteral (2245579571013551) 25000000000000000),
          (exactRationalLiteral (175874103545259347) 2400000000000000000),
          (exactRationalLiteral (935115395819363) 60000000000000000),
          (exactRationalLiteral (70117963185209) 25000000000000000),
          (exactRationalLiteral (32311830911515151) 19200000000000000000),
          (exactRationalLiteral (14681315697281251) 19200000000000000000),
          (exactRationalLiteral (491369776554449) 150000000000000000),
          (exactRationalLiteral (852892143896321) 300000000000000000),
          (exactRationalLiteral (26426324098173) 2000000000000000),
          (exactRationalLiteral (1380077089899599) 300000000000000000),
          (exactRationalLiteral (192222039291901) 60000000000000000),
          (exactRationalLiteral (9902845243595809) 1920000000000000000),
          (exactRationalLiteral (302110623372723119) 19200000000000000000),
          (exactRationalLiteral (148070130539370687) 3200000000000000000),
          (exactRationalLiteral (703185794199835157) 4800000000000000000),
          (exactRationalLiteral (3332621700982323511) 19200000000000000000),
          (exactRationalLiteral (1548364581206023) 75000000000000000),
          (exactRationalLiteral (23914269397210939) 6400000000000000000),
          (exactRationalLiteral (5321122956166937723) 19200000000000000000),
          (exactRationalLiteral (74885077364170521) 128000000000000000),
          (exactRationalLiteral (5321122956166937723) 19200000000000000000),
          (exactRationalLiteral (23914269397210939) 6400000000000000000),
          (exactRationalLiteral (1548364581206023) 75000000000000000),
          (exactRationalLiteral (3332621700982323511) 19200000000000000000),
          (exactRationalLiteral (703185794199835157) 4800000000000000000),
          (exactRationalLiteral (148070130539370687) 3200000000000000000),
          (exactRationalLiteral (302110623372723119) 19200000000000000000),
          (exactRationalLiteral (9902845243595809) 1920000000000000000),
          (exactRationalLiteral (192222039291901) 60000000000000000),
          (exactRationalLiteral (1380077089899599) 300000000000000000),
          (exactRationalLiteral (26426324098173) 2000000000000000),
          (exactRationalLiteral (852892143896321) 300000000000000000),
          (exactRationalLiteral (491369776554449) 150000000000000000),
          (exactRationalLiteral (14681315697281251) 19200000000000000000),
          (exactRationalLiteral (32311830911515151) 19200000000000000000),
          (exactRationalLiteral (70117963185209) 25000000000000000),
          (exactRationalLiteral (935115395819363) 60000000000000000),
          (exactRationalLiteral (175874103545259347) 2400000000000000000),
          (exactRationalLiteral (2245579571013551) 25000000000000000),
          (exactRationalLiteral (5698382773389209) 300000000000000000),
          (exactRationalLiteral (400791461043800521) 19200000000000000000),
          (exactRationalLiteral (101673746728037) 640000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (42, 10),
      (42, 14),
      (42, 18),
      (42, 22)
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
            (exactRationalLiteral (2745191161656999) 327680000000000000),
            (exactRationalLiteral (-2745191161656999) 102400000000000000),
            (exactRationalLiteral (915063720552333) 32000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (28253500296969814687) 1228800000000000000000),
            (exactRationalLiteral (1578998522154039023) 25600000000000000000),
            (exactRationalLiteral (-216962220034528193) 1600000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-25938226347782440399) 307200000000000000000),
            (exactRationalLiteral (21646247607089877) 6400000000000000000),
            (exactRationalLiteral (100640701113494969) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (22562061826773728911) 409600000000000000000),
            (exactRationalLiteral (-2729090569732826403) 25600000000000000000),
            (exactRationalLiteral (-364918385707221747) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (887833322449429463) 307200000000000000000),
            (exactRationalLiteral (586012201102644207) 6400000000000000000),
            (exactRationalLiteral (41236053179788679) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-238497993848573393) 51200000000000000000),
            (exactRationalLiteral (-85315770436761279) 3200000000000000000),
            (exactRationalLiteral (-4647007310535627) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (-44459486181197713) 204800000000000000000),
            (exactRationalLiteral (66918580980469149) 12800000000000000000),
            (exactRationalLiteral (3844181773949421) 800000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-210198630695183389) 245760000000000000000),
            (exactRationalLiteral (-46090560034033889) 25600000000000000000),
            (exactRationalLiteral (-2430354942403121) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (439400943590078929) 1228800000000000000000),
            (exactRationalLiteral (20540828224004657) 25600000000000000000),
            (exactRationalLiteral (836528018207377) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2818018677483109273) 1228800000000000000000),
            (exactRationalLiteral (15455435204911593) 25600000000000000000),
            (exactRationalLiteral (-1315660222867) 12800000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (734078491507929883) 614400000000000000000),
            (exactRationalLiteral (168674259969423) 102400000000000000),
            (exactRationalLiteral (363639182312203) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-10651851921474279) 1024000000000000000),
            (exactRationalLiteral (-783272497007759) 320000000000000000),
            (exactRationalLiteral (-19102866625653) 20000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-2672997971590322047) 614400000000000000000),
            (exactRationalLiteral (10010713122825161) 12800000000000000000),
            (exactRationalLiteral (-317523198734959) 800000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-87764724385049017) 122880000000000000000),
            (exactRationalLiteral (10832161884187631) 2560000000000000000),
            (exactRationalLiteral (-355444333809293) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-6609310979312220079) 614400000000000000000),
            (exactRationalLiteral (114926745051122577) 12800000000000000000),
            (exactRationalLiteral (-1087516152571183) 800000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8753552725753210741) 245760000000000000000),
            (exactRationalLiteral (172652625891225499) 5120000000000000000),
            (exactRationalLiteral (-6632548851536297) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-241763552181034321) 24576000000000000000),
            (exactRationalLiteral (3290931996496890327) 12800000000000000000),
            (exactRationalLiteral (-278093946735222121) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (188214172883340410561) 307200000000000000000),
            (exactRationalLiteral (-1748406744852276011) 1280000000000000000),
            (exactRationalLiteral (104780457911501341) 80000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-333734128401936120351) 409600000000000000000),
            (exactRationalLiteral (46844012589976301059) 25600000000000000000),
            (exactRationalLiteral (-543057314642964153) 320000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (85366600761857006147) 307200000000000000000),
            (exactRationalLiteral (-5636114454667447749) 6400000000000000000),
            (exactRationalLiteral (353805892268191667) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-24806758220066598737) 1228800000000000000000),
            (exactRationalLiteral (2469853301994606047) 25600000000000000000),
            (exactRationalLiteral (-192995547488356337) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-539320590994435610281) 1228800000000000000000),
            (exactRationalLiteral (8141690427935540151) 25600000000000000000),
            (exactRationalLiteral (-231827241624291817) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (555370613315430494977) 614400000000000000000),
            (exactRationalLiteral (-7761254685770180639) 12800000000000000000),
            (exactRationalLiteral (39257075522350733) 160000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-539320590994435610281) 1228800000000000000000),
            (exactRationalLiteral (8141690427935540151) 25600000000000000000),
            (exactRationalLiteral (-231827241624291817) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-24806758220066598737) 1228800000000000000000),
            (exactRationalLiteral (2469853301994606047) 25600000000000000000),
            (exactRationalLiteral (-192995547488356337) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (85366600761857006147) 307200000000000000000),
            (exactRationalLiteral (-5636114454667447749) 6400000000000000000),
            (exactRationalLiteral (353805892268191667) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-333734128401936120351) 409600000000000000000),
            (exactRationalLiteral (46844012589976301059) 25600000000000000000),
            (exactRationalLiteral (-543057314642964153) 320000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (188214172883340410561) 307200000000000000000),
            (exactRationalLiteral (-1748406744852276011) 1280000000000000000),
            (exactRationalLiteral (104780457911501341) 80000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-241763552181034321) 24576000000000000000),
            (exactRationalLiteral (3290931996496890327) 12800000000000000000),
            (exactRationalLiteral (-278093946735222121) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-8753552725753210741) 245760000000000000000),
            (exactRationalLiteral (172652625891225499) 5120000000000000000),
            (exactRationalLiteral (-6632548851536297) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-6609310979312220079) 614400000000000000000),
            (exactRationalLiteral (114926745051122577) 12800000000000000000),
            (exactRationalLiteral (-1087516152571183) 800000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-87764724385049017) 122880000000000000000),
            (exactRationalLiteral (10832161884187631) 2560000000000000000),
            (exactRationalLiteral (-355444333809293) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2672997971590322047) 614400000000000000000),
            (exactRationalLiteral (10010713122825161) 12800000000000000000),
            (exactRationalLiteral (-317523198734959) 800000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-10651851921474279) 1024000000000000000),
            (exactRationalLiteral (-783272497007759) 320000000000000000),
            (exactRationalLiteral (-19102866625653) 20000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (734078491507929883) 614400000000000000000),
            (exactRationalLiteral (168674259969423) 102400000000000000),
            (exactRationalLiteral (363639182312203) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2818018677483109273) 1228800000000000000000),
            (exactRationalLiteral (15455435204911593) 25600000000000000000),
            (exactRationalLiteral (-1315660222867) 12800000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (439400943590078929) 1228800000000000000000),
            (exactRationalLiteral (20540828224004657) 25600000000000000000),
            (exactRationalLiteral (836528018207377) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-210198630695183389) 245760000000000000000),
            (exactRationalLiteral (-46090560034033889) 25600000000000000000),
            (exactRationalLiteral (-2430354942403121) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-44459486181197713) 204800000000000000000),
            (exactRationalLiteral (66918580980469149) 12800000000000000000),
            (exactRationalLiteral (3844181773949421) 800000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-238497993848573393) 51200000000000000000),
            (exactRationalLiteral (-85315770436761279) 3200000000000000000),
            (exactRationalLiteral (-4647007310535627) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (887833322449429463) 307200000000000000000),
            (exactRationalLiteral (586012201102644207) 6400000000000000000),
            (exactRationalLiteral (41236053179788679) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (22562061826773728911) 409600000000000000000),
            (exactRationalLiteral (-2729090569732826403) 25600000000000000000),
            (exactRationalLiteral (-364918385707221747) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-25938226347782440399) 307200000000000000000),
            (exactRationalLiteral (21646247607089877) 6400000000000000000),
            (exactRationalLiteral (100640701113494969) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (28253500296969814687) 1228800000000000000000),
            (exactRationalLiteral (1578998522154039023) 25600000000000000000),
            (exactRationalLiteral (-216962220034528193) 1600000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (2745191161656999) 327680000000000000),
            (exactRationalLiteral (-2745191161656999) 102400000000000000),
            (exactRationalLiteral (915063720552333) 32000000000000000),
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
          (exactRationalLiteral (4044709554609439703) 153600000000000000000),
          (exactRationalLiteral (13578914438238257) 160000000000000000),
          (exactRationalLiteral (6080899191886277) 100000000000000000),
          (exactRationalLiteral (114970807284665353) 12800000000000000000),
          (exactRationalLiteral (4916303449796861) 768000000000000000),
          (exactRationalLiteral (19559906505071) 37500000000000000),
          (exactRationalLiteral (149439299162002633) 153600000000000000000),
          (exactRationalLiteral (62896425211549793) 153600000000000000000),
          (exactRationalLiteral (358009517861658961) 153600000000000000000),
          (exactRationalLiteral (33265351991268869) 25600000000000000000),
          (exactRationalLiteral (50682323034660913) 4800000000000000000),
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
          (exactRationalLiteral (50682323034660913) 4800000000000000000),
          (exactRationalLiteral (33265351991268869) 25600000000000000000),
          (exactRationalLiteral (358009517861658961) 153600000000000000000),
          (exactRationalLiteral (62896425211549793) 153600000000000000000),
          (exactRationalLiteral (149439299162002633) 153600000000000000000),
          (exactRationalLiteral (19559906505071) 37500000000000000),
          (exactRationalLiteral (4916303449796861) 768000000000000000),
          (exactRationalLiteral (114970807284665353) 12800000000000000000),
          (exactRationalLiteral (6080899191886277) 100000000000000000),
          (exactRationalLiteral (13578914438238257) 160000000000000000),
          (exactRationalLiteral (4044709554609439703) 153600000000000000000),
          (exactRationalLiteral (101673746728037) 10000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 3),
      (37, 11),
      (37, 19),
      (37, 27)
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
            (exactRationalLiteral (223377221561497289) 40960000000000000000),
            (exactRationalLiteral (-51548589591114759) 2560000000000000000),
            (exactRationalLiteral (3965276122393443) 160000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (7053696531571414817) 245760000000000000000),
            (exactRationalLiteral (783418576204608039) 25600000000000000000),
            (exactRationalLiteral (-180827752940187299) 1600000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-24688679848093387069) 307200000000000000000),
            (exactRationalLiteral (380199352403356973) 6400000000000000000),
            (exactRationalLiteral (78635851284638579) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (15795174511144332917) 409600000000000000000),
            (exactRationalLiteral (-3962313062563997691) 25600000000000000000),
            (exactRationalLiteral (-251692860708363897) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (4816509483504681661) 307200000000000000000),
            (exactRationalLiteral (709841571962760327) 6400000000000000000),
            (exactRationalLiteral (20678632250269381) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-1266179693266805801) 153600000000000000000),
            (exactRationalLiteral (-95417300365948999) 3200000000000000000),
            (exactRationalLiteral (-403757654058233) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (59441204950812467) 122880000000000000000),
            (exactRationalLiteral (73766716139990597) 12800000000000000000),
            (exactRationalLiteral (-420114194188697) 800000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1348368732115302443) 1228800000000000000000),
            (exactRationalLiteral (-51645959366818729) 25600000000000000000),
            (exactRationalLiteral (-347344723989299) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (569791364158061899) 1228800000000000000000),
            (exactRationalLiteral (22440497799567417) 25600000000000000000),
            (exactRationalLiteral (113306769574003) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (970084685803433473) 409600000000000000000),
            (exactRationalLiteral (15535734609489137) 25600000000000000000),
            (exactRationalLiteral (204607230147147) 1600000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (864517386649165481) 614400000000000000000),
            (exactRationalLiteral (22323604213637643) 12800000000000000000),
            (exactRationalLiteral (256021676417681) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-823474392934362899) 76800000000000000000),
            (exactRationalLiteral (-4268995775561867) 1600000000000000000),
            (exactRationalLiteral (-80802312133271) 100000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-2617667358117965621) 614400000000000000000),
            (exactRationalLiteral (8278926887997809) 12800000000000000000),
            (exactRationalLiteral (-548369918678717) 800000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-39208879239284341) 204800000000000000000),
            (exactRationalLiteral (52987761929438307) 12800000000000000000),
            (exactRationalLiteral (-231079411940631) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-5932544737228177397) 614400000000000000000),
            (exactRationalLiteral (110704663244918553) 12800000000000000000),
            (exactRationalLiteral (-1023524750530829) 800000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-38677677071942887379) 1228800000000000000000),
            (exactRationalLiteral (831782117202400767) 25600000000000000000),
            (exactRationalLiteral (-9107957275327067) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (3508527776893029711) 204800000000000000000),
            (exactRationalLiteral (2259159968079137167) 12800000000000000000),
            (exactRationalLiteral (-237792067473654459) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (141778927537551314507) 307200000000000000000),
            (exactRationalLiteral (-6781359803486801327) 6400000000000000000),
            (exactRationalLiteral (456434670829782659) 400000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-751353086143622608783) 1228800000000000000000),
            (exactRationalLiteral (36667197497569915547) 25600000000000000000),
            (exactRationalLiteral (-2373120972988371991) 1600000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (11122659453028359853) 61440000000000000000),
            (exactRationalLiteral (-4312034623559091277) 6400000000000000000),
            (exactRationalLiteral (308234023285986569) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-4065231010250309753) 409600000000000000000),
            (exactRationalLiteral (1751817085645335319) 25600000000000000000),
            (exactRationalLiteral (-166022560686279027) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-493166748120378504083) 1228800000000000000000),
            (exactRationalLiteral (7257195064406056431) 25600000000000000000),
            (exactRationalLiteral (-210420440140450043) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (170364026300578951881) 204800000000000000000),
            (exactRationalLiteral (-7009328590529965719) 12800000000000000000),
            (exactRationalLiteral (35935534001670759) 160000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-493166748120378504083) 1228800000000000000000),
            (exactRationalLiteral (7257195064406056431) 25600000000000000000),
            (exactRationalLiteral (-210420440140450043) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-4065231010250309753) 409600000000000000000),
            (exactRationalLiteral (1751817085645335319) 25600000000000000000),
            (exactRationalLiteral (-166022560686279027) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (11122659453028359853) 61440000000000000000),
            (exactRationalLiteral (-4312034623559091277) 6400000000000000000),
            (exactRationalLiteral (308234023285986569) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-751353086143622608783) 1228800000000000000000),
            (exactRationalLiteral (36667197497569915547) 25600000000000000000),
            (exactRationalLiteral (-2373120972988371991) 1600000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (141778927537551314507) 307200000000000000000),
            (exactRationalLiteral (-6781359803486801327) 6400000000000000000),
            (exactRationalLiteral (456434670829782659) 400000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (3508527776893029711) 204800000000000000000),
            (exactRationalLiteral (2259159968079137167) 12800000000000000000),
            (exactRationalLiteral (-237792067473654459) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-38677677071942887379) 1228800000000000000000),
            (exactRationalLiteral (831782117202400767) 25600000000000000000),
            (exactRationalLiteral (-9107957275327067) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-5932544737228177397) 614400000000000000000),
            (exactRationalLiteral (110704663244918553) 12800000000000000000),
            (exactRationalLiteral (-1023524750530829) 800000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-39208879239284341) 204800000000000000000),
            (exactRationalLiteral (52987761929438307) 12800000000000000000),
            (exactRationalLiteral (-231079411940631) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2617667358117965621) 614400000000000000000),
            (exactRationalLiteral (8278926887997809) 12800000000000000000),
            (exactRationalLiteral (-548369918678717) 800000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-823474392934362899) 76800000000000000000),
            (exactRationalLiteral (-4268995775561867) 1600000000000000000),
            (exactRationalLiteral (-80802312133271) 100000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (864517386649165481) 614400000000000000000),
            (exactRationalLiteral (22323604213637643) 12800000000000000000),
            (exactRationalLiteral (256021676417681) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (970084685803433473) 409600000000000000000),
            (exactRationalLiteral (15535734609489137) 25600000000000000000),
            (exactRationalLiteral (204607230147147) 1600000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (569791364158061899) 1228800000000000000000),
            (exactRationalLiteral (22440497799567417) 25600000000000000000),
            (exactRationalLiteral (113306769574003) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1348368732115302443) 1228800000000000000000),
            (exactRationalLiteral (-51645959366818729) 25600000000000000000),
            (exactRationalLiteral (-347344723989299) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (59441204950812467) 122880000000000000000),
            (exactRationalLiteral (73766716139990597) 12800000000000000000),
            (exactRationalLiteral (-420114194188697) 800000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1266179693266805801) 153600000000000000000),
            (exactRationalLiteral (-95417300365948999) 3200000000000000000),
            (exactRationalLiteral (-403757654058233) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (4816509483504681661) 307200000000000000000),
            (exactRationalLiteral (709841571962760327) 6400000000000000000),
            (exactRationalLiteral (20678632250269381) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (15795174511144332917) 409600000000000000000),
            (exactRationalLiteral (-3962313062563997691) 25600000000000000000),
            (exactRationalLiteral (-251692860708363897) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-24688679848093387069) 307200000000000000000),
            (exactRationalLiteral (380199352403356973) 6400000000000000000),
            (exactRationalLiteral (78635851284638579) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (7053696531571414817) 245760000000000000000),
            (exactRationalLiteral (783418576204608039) 25600000000000000000),
            (exactRationalLiteral (-180827752940187299) 1600000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (223377221561497289) 40960000000000000000),
            (exactRationalLiteral (-51548589591114759) 2560000000000000000),
            (exactRationalLiteral (3965276122393443) 160000000000000000),
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
          (exactRationalLiteral (34874095127716691) 5120000000000000000),
          (exactRationalLiteral (579598786893711043) 19200000000000000000),
          (exactRationalLiteral (3197795990816889257) 38400000000000000000),
          (exactRationalLiteral (2435865474020852967) 51200000000000000000),
          (exactRationalLiteral (109340490401234549) 4800000000000000000),
          (exactRationalLiteral (161616796093603) 16000000000000000),
          (exactRationalLiteral (2682883763580203) 3200000000000000000),
          (exactRationalLiteral (23489174051226869) 19200000000000000000),
          (exactRationalLiteral (9954549488143273) 19200000000000000000),
          (exactRationalLiteral (46213431489190813) 19200000000000000000),
          (exactRationalLiteral (14565663368224753) 9600000000000000000),
          (exactRationalLiteral (8713712824864071) 800000000000000000),
          (exactRationalLiteral (22033615209816861) 5120000000000000000),
          (exactRationalLiteral (34668168025365521) 76800000000000000000),
          (exactRationalLiteral (52231344140962881) 5120000000000000000),
          (exactRationalLiteral (5149888698895521937) 153600000000000000000),
          (exactRationalLiteral (259528718314473767) 9600000000000000000),
          (exactRationalLiteral (20440755596233116061) 38400000000000000000),
          (exactRationalLiteral (108580640544426336973) 153600000000000000000),
          (exactRationalLiteral (8687111142521016919) 38400000000000000000),
          (exactRationalLiteral (2245337307893351369) 153600000000000000000),
          (exactRationalLiteral (21482512418114997683) 51200000000000000000),
          (exactRationalLiteral (13316685038428837853) 15360000000000000000),
          (exactRationalLiteral (21482512418114997683) 51200000000000000000),
          (exactRationalLiteral (2245337307893351369) 153600000000000000000),
          (exactRationalLiteral (8687111142521016919) 38400000000000000000),
          (exactRationalLiteral (108580640544426336973) 153600000000000000000),
          (exactRationalLiteral (20440755596233116061) 38400000000000000000),
          (exactRationalLiteral (259528718314473767) 9600000000000000000),
          (exactRationalLiteral (5149888698895521937) 153600000000000000000),
          (exactRationalLiteral (52231344140962881) 5120000000000000000),
          (exactRationalLiteral (34668168025365521) 76800000000000000000),
          (exactRationalLiteral (22033615209816861) 5120000000000000000),
          (exactRationalLiteral (8713712824864071) 800000000000000000),
          (exactRationalLiteral (14565663368224753) 9600000000000000000),
          (exactRationalLiteral (46213431489190813) 19200000000000000000),
          (exactRationalLiteral (9954549488143273) 19200000000000000000),
          (exactRationalLiteral (23489174051226869) 19200000000000000000),
          (exactRationalLiteral (2682883763580203) 3200000000000000000),
          (exactRationalLiteral (161616796093603) 16000000000000000),
          (exactRationalLiteral (109340490401234549) 4800000000000000000),
          (exactRationalLiteral (2435865474020852967) 51200000000000000000),
          (exactRationalLiteral (3197795990816889257) 38400000000000000000),
          (exactRationalLiteral (579598786893711043) 19200000000000000000),
          (exactRationalLiteral (34874095127716691) 5120000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 18),
      (37, 26)
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
            (exactRationalLiteral (135327756895017247) 40960000000000000000),
            (exactRationalLiteral (-36907570062277431) 2560000000000000000),
            (exactRationalLiteral (3355233642025221) 160000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (37943598948179838307) 1228800000000000000000),
            (exactRationalLiteral (132376498632540631) 25600000000000000000),
            (exactRationalLiteral (-28938657169169281) 320000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-21551872917573007843) 307200000000000000000),
            (exactRationalLiteral (650733057884198509) 6400000000000000000),
            (exactRationalLiteral (56631001455782189) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (7014744309848025747) 409600000000000000000),
            (exactRationalLiteral (-4742633455399737579) 25600000000000000000),
            (exactRationalLiteral (-138467335709506047) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (3080490939522133001) 102400000000000000000),
            (exactRationalLiteral (150288251820959851) 1280000000000000000),
            (exactRationalLiteral (121211320750083) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-365311117737057803) 30720000000000000000),
            (exactRationalLiteral (-88545831669227143) 3200000000000000000),
            (exactRationalLiteral (3839492002419161) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (717707767391189081) 614400000000000000000),
            (exactRationalLiteral (63557667426959573) 12800000000000000000),
            (exactRationalLiteral (-936882032465363) 160000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1654080584130431117) 1228800000000000000000),
            (exactRationalLiteral (-48869317825948281) 25600000000000000000),
            (exactRationalLiteral (1735665494424523) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (702901147195820941) 1228800000000000000000),
            (exactRationalLiteral (21447282380596681) 25600000000000000000),
            (exactRationalLiteral (-609914479059371) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (3007400010861023093) 1228800000000000000000),
            (exactRationalLiteral (17092293046088769) 25600000000000000000),
            (exactRationalLiteral (573671988152669) 1600000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (333700267341475141) 204800000000000000000),
            (exactRationalLiteral (23132455907519323) 12800000000000000000),
            (exactRationalLiteral (148404170523159) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-849999147249353377) 76800000000000000000),
            (exactRationalLiteral (-4562780982104963) 1600000000000000000),
            (exactRationalLiteral (-66090291138277) 100000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-858499207564632801) 204800000000000000000),
            (exactRationalLiteral (224950150935817) 512000000000000000),
            (exactRationalLiteral (-31168665544899) 32000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (39604888120592779) 122880000000000000000),
            (exactRationalLiteral (52312174125413107) 12800000000000000000),
            (exactRationalLiteral (-106714490071969) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1760114363052291537) 204800000000000000000),
            (exactRationalLiteral (21347709409375189) 2560000000000000000),
            (exactRationalLiteral (-38381333939619) 32000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-33806181489727570661) 1228800000000000000000),
            (exactRationalLiteral (790399471253510959) 25600000000000000000),
            (exactRationalLiteral (-11583365699117837) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (855529833860653171) 24576000000000000000),
            (exactRationalLiteral (277719091341530931) 2560000000000000000),
            (exactRationalLiteral (-197490188212086797) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (106298114291677002269) 307200000000000000000),
            (exactRationalLiteral (-5090556357623118783) 6400000000000000000),
            (exactRationalLiteral (388967052102058613) 400000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-558458690433157784297) 1228800000000000000000),
            (exactRationalLiteral (27859044806069325131) 25600000000000000000),
            (exactRationalLiteral (-2030955372761923217) 1600000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (33257610327290270039) 307200000000000000000),
            (exactRationalLiteral (-3170242268379555197) 6400000000000000000),
            (exactRationalLiteral (262662154303781471) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-3569169297905956429) 1228800000000000000000),
            (exactRationalLiteral (1141672816504373831) 25600000000000000000),
            (exactRationalLiteral (-139049573884201717) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-150687665269897399639) 409600000000000000000),
            (exactRationalLiteral (6458326906811939807) 25600000000000000000),
            (exactRationalLiteral (-189013638656608269) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (471125808568243707389) 614400000000000000000),
            (exactRationalLiteral (-6323833325703350279) 12800000000000000000),
            (exactRationalLiteral (6522798496198157) 32000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-150687665269897399639) 409600000000000000000),
            (exactRationalLiteral (6458326906811939807) 25600000000000000000),
            (exactRationalLiteral (-189013638656608269) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-3569169297905956429) 1228800000000000000000),
            (exactRationalLiteral (1141672816504373831) 25600000000000000000),
            (exactRationalLiteral (-139049573884201717) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (33257610327290270039) 307200000000000000000),
            (exactRationalLiteral (-3170242268379555197) 6400000000000000000),
            (exactRationalLiteral (262662154303781471) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-558458690433157784297) 1228800000000000000000),
            (exactRationalLiteral (27859044806069325131) 25600000000000000000),
            (exactRationalLiteral (-2030955372761923217) 1600000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (106298114291677002269) 307200000000000000000),
            (exactRationalLiteral (-5090556357623118783) 6400000000000000000),
            (exactRationalLiteral (388967052102058613) 400000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (855529833860653171) 24576000000000000000),
            (exactRationalLiteral (277719091341530931) 2560000000000000000),
            (exactRationalLiteral (-197490188212086797) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-33806181489727570661) 1228800000000000000000),
            (exactRationalLiteral (790399471253510959) 25600000000000000000),
            (exactRationalLiteral (-11583365699117837) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-1760114363052291537) 204800000000000000000),
            (exactRationalLiteral (21347709409375189) 2560000000000000000),
            (exactRationalLiteral (-38381333939619) 32000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (39604888120592779) 122880000000000000000),
            (exactRationalLiteral (52312174125413107) 12800000000000000000),
            (exactRationalLiteral (-106714490071969) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-858499207564632801) 204800000000000000000),
            (exactRationalLiteral (224950150935817) 512000000000000000),
            (exactRationalLiteral (-31168665544899) 32000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-849999147249353377) 76800000000000000000),
            (exactRationalLiteral (-4562780982104963) 1600000000000000000),
            (exactRationalLiteral (-66090291138277) 100000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (333700267341475141) 204800000000000000000),
            (exactRationalLiteral (23132455907519323) 12800000000000000000),
            (exactRationalLiteral (148404170523159) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3007400010861023093) 1228800000000000000000),
            (exactRationalLiteral (17092293046088769) 25600000000000000000),
            (exactRationalLiteral (573671988152669) 1600000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (702901147195820941) 1228800000000000000000),
            (exactRationalLiteral (21447282380596681) 25600000000000000000),
            (exactRationalLiteral (-609914479059371) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1654080584130431117) 1228800000000000000000),
            (exactRationalLiteral (-48869317825948281) 25600000000000000000),
            (exactRationalLiteral (1735665494424523) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (717707767391189081) 614400000000000000000),
            (exactRationalLiteral (63557667426959573) 12800000000000000000),
            (exactRationalLiteral (-936882032465363) 160000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-365311117737057803) 30720000000000000000),
            (exactRationalLiteral (-88545831669227143) 3200000000000000000),
            (exactRationalLiteral (3839492002419161) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (3080490939522133001) 102400000000000000000),
            (exactRationalLiteral (150288251820959851) 1280000000000000000),
            (exactRationalLiteral (121211320750083) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (7014744309848025747) 409600000000000000000),
            (exactRationalLiteral (-4742633455399737579) 25600000000000000000),
            (exactRationalLiteral (-138467335709506047) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-21551872917573007843) 307200000000000000000),
            (exactRationalLiteral (650733057884198509) 6400000000000000000),
            (exactRationalLiteral (56631001455782189) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (37943598948179838307) 1228800000000000000000),
            (exactRationalLiteral (132376498632540631) 25600000000000000000),
            (exactRationalLiteral (-28938657169169281) 320000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (135327756895017247) 40960000000000000000),
            (exactRationalLiteral (-36907570062277431) 2560000000000000000),
            (exactRationalLiteral (3355233642025221) 160000000000000000),
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
          (exactRationalLiteral (2387662593694440931) 76800000000000000000),
          (exactRationalLiteral (182212317671436161) 2400000000000000000),
          (exactRationalLiteral (181250617323517411) 6400000000000000000),
          (exactRationalLiteral (1435735189922285921) 38400000000000000000),
          (exactRationalLiteral (259819122857184283) 19200000000000000000),
          (exactRationalLiteral (111524423900127287) 76800000000000000000),
          (exactRationalLiteral (44861000900394887) 30720000000000000000),
          (exactRationalLiteral (95631455034514523) 153600000000000000000),
          (exactRationalLiteral (127524268264281257) 51200000000000000000),
          (exactRationalLiteral (133861196688200701) 76800000000000000000),
          (exactRationalLiteral (33745250197601) 3000000000000000),
          (exactRationalLiteral (40540486102655941) 9600000000000000000),
          (exactRationalLiteral (2955858349749347) 5120000000000000000),
          (exactRationalLiteral (87554208219437407) 9600000000000000000),
          (exactRationalLiteral (565795192130836901) 19200000000000000000),
          (exactRationalLiteral (208180938263615139) 5120000000000000000),
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
          (exactRationalLiteral (208180938263615139) 5120000000000000000),
          (exactRationalLiteral (565795192130836901) 19200000000000000000),
          (exactRationalLiteral (87554208219437407) 9600000000000000000),
          (exactRationalLiteral (2955858349749347) 5120000000000000000),
          (exactRationalLiteral (40540486102655941) 9600000000000000000),
          (exactRationalLiteral (33745250197601) 3000000000000000),
          (exactRationalLiteral (133861196688200701) 76800000000000000000),
          (exactRationalLiteral (127524268264281257) 51200000000000000000),
          (exactRationalLiteral (95631455034514523) 153600000000000000000),
          (exactRationalLiteral (44861000900394887) 30720000000000000000),
          (exactRationalLiteral (111524423900127287) 76800000000000000000),
          (exactRationalLiteral (259819122857184283) 19200000000000000000),
          (exactRationalLiteral (1435735189922285921) 38400000000000000000),
          (exactRationalLiteral (181250617323517411) 6400000000000000000),
          (exactRationalLiteral (182212317671436161) 2400000000000000000),
          (exactRationalLiteral (2387662593694440931) 76800000000000000000),
          (exactRationalLiteral (2745191161656999) 640000000000000000),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ),
          (0 : ℚ)
        ]
      }
    roots := ![
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
      (37, 17),
      (37, 25)
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
            (exactRationalLiteral (74120161364738973) 40960000000000000000),
            (exactRationalLiteral (-24706720454912991) 2560000000000000000),
            (exactRationalLiteral (2745191161656999) 160000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (37146076378202288809) 1228800000000000000000),
            (exactRationalLiteral (-374127710562163201) 25600000000000000000),
            (exactRationalLiteral (-108558818751505511) 1600000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-17055921952113856081) 307200000000000000000),
            (exactRationalLiteral (166649472809922897) 1280000000000000000),
            (exactRationalLiteral (34626151626925799) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-2873424577124329799) 409600000000000000000),
            (exactRationalLiteral (-5070051748240046067) 25600000000000000000),
            (exactRationalLiteral (-25241810710648197) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (13669345225326118337) 307200000000000000000),
            (exactRationalLiteral (710811262528760991) 6400000000000000000),
            (exactRationalLiteral (-4087241921753843) 80000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-152985578403047491) 10240000000000000000),
            (exactRationalLiteral (-64701364346595711) 3200000000000000000),
            (exactRationalLiteral (1616548331779311) 40000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (341927888710824089) 204800000000000000000),
            (exactRationalLiteral (36291434841376077) 12800000000000000000),
            (exactRationalLiteral (-8948706130464933) 800000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1918136464279371239) 1228800000000000000000),
            (exactRationalLiteral (-7552127082284509) 5120000000000000000),
            (exactRationalLiteral (763735142567669) 320000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (821372982736155079) 1228800000000000000000),
            (exactRationalLiteral (17561181967092449) 25600000000000000000),
            (exactRationalLiteral (-266627145538549) 320000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (3118314092027409823) 1228800000000000000000),
            (exactRationalLiteral (20125110514710489) 25600000000000000000),
            (exactRationalLiteral (942736746158191) 1600000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1141245917492241181) 614400000000000000000),
            (exactRationalLiteral (4702167515564583) 2560000000000000000),
            (exactRationalLiteral (40786664628637) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-292703356183887501) 25600000000000000000),
            (exactRationalLiteral (-4797718104668083) 1600000000000000000),
            (exactRationalLiteral (-51378270143283) 100000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-510405817319354117) 122880000000000000000),
            (exactRationalLiteral (2045193779018009) 12800000000000000000),
            (exactRationalLiteral (-1010063358566233) 800000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (511114371162053557) 614400000000000000000),
            (exactRationalLiteral (10426809201772511) 2560000000000000000),
            (exactRationalLiteral (17650431796693) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-186046809657973729) 24576000000000000000),
            (exactRationalLiteral (103028396456994753) 12800000000000000000),
            (exactRationalLiteral (-895541946450121) 800000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-29212686684291082031) 1228800000000000000000),
            (exactRationalLiteral (739115191609458071) 25600000000000000000),
            (exactRationalLiteral (-14058774122908607) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (27511143845263486289) 614400000000000000000),
            (exactRationalLiteral (679238462382442791) 12800000000000000000),
            (exactRationalLiteral (-31437661790103827) 160000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (80152510296252096743) 307200000000000000000),
            (exactRationalLiteral (-3669623386670332423) 6400000000000000000),
            (exactRationalLiteral (321499433374334567) 400000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-138102407889659705673) 409600000000000000000),
            (exactRationalLiteral (20419554515474529811) 25600000000000000000),
            (exactRationalLiteral (-1688789772535474443) 1600000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (17205815092729496117) 307200000000000000000),
            (exactRationalLiteral (-2210737389128839509) 6400000000000000000),
            (exactRationalLiteral (217090285321576373) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (1720164661718175193) 1228800000000000000000),
            (exactRationalLiteral (639420494571721583) 25600000000000000000),
            (exactRationalLiteral (-112076587082124407) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-415495570826764492207) 1228800000000000000000),
            (exactRationalLiteral (5745085955153190279) 25600000000000000000),
            (exactRationalLiteral (-33521367434553299) 320000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (87014643466493890667) 122880000000000000000),
            (exactRationalLiteral (-5704768891290334319) 12800000000000000000),
            (exactRationalLiteral (29292450960310811) 160000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-415495570826764492207) 1228800000000000000000),
            (exactRationalLiteral (5745085955153190279) 25600000000000000000),
            (exactRationalLiteral (-33521367434553299) 320000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1720164661718175193) 1228800000000000000000),
            (exactRationalLiteral (639420494571721583) 25600000000000000000),
            (exactRationalLiteral (-112076587082124407) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (17205815092729496117) 307200000000000000000),
            (exactRationalLiteral (-2210737389128839509) 6400000000000000000),
            (exactRationalLiteral (217090285321576373) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-138102407889659705673) 409600000000000000000),
            (exactRationalLiteral (20419554515474529811) 25600000000000000000),
            (exactRationalLiteral (-1688789772535474443) 1600000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (80152510296252096743) 307200000000000000000),
            (exactRationalLiteral (-3669623386670332423) 6400000000000000000),
            (exactRationalLiteral (321499433374334567) 400000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (27511143845263486289) 614400000000000000000),
            (exactRationalLiteral (679238462382442791) 12800000000000000000),
            (exactRationalLiteral (-31437661790103827) 160000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-29212686684291082031) 1228800000000000000000),
            (exactRationalLiteral (739115191609458071) 25600000000000000000),
            (exactRationalLiteral (-14058774122908607) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-186046809657973729) 24576000000000000000),
            (exactRationalLiteral (103028396456994753) 12800000000000000000),
            (exactRationalLiteral (-895541946450121) 800000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (511114371162053557) 614400000000000000000),
            (exactRationalLiteral (10426809201772511) 2560000000000000000),
            (exactRationalLiteral (17650431796693) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-510405817319354117) 122880000000000000000),
            (exactRationalLiteral (2045193779018009) 12800000000000000000),
            (exactRationalLiteral (-1010063358566233) 800000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-292703356183887501) 25600000000000000000),
            (exactRationalLiteral (-4797718104668083) 1600000000000000000),
            (exactRationalLiteral (-51378270143283) 100000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (1141245917492241181) 614400000000000000000),
            (exactRationalLiteral (4702167515564583) 2560000000000000000),
            (exactRationalLiteral (40786664628637) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3118314092027409823) 1228800000000000000000),
            (exactRationalLiteral (20125110514710489) 25600000000000000000),
            (exactRationalLiteral (942736746158191) 1600000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (821372982736155079) 1228800000000000000000),
            (exactRationalLiteral (17561181967092449) 25600000000000000000),
            (exactRationalLiteral (-266627145538549) 320000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-1918136464279371239) 1228800000000000000000),
            (exactRationalLiteral (-7552127082284509) 5120000000000000000),
            (exactRationalLiteral (763735142567669) 320000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (341927888710824089) 204800000000000000000),
            (exactRationalLiteral (36291434841376077) 12800000000000000000),
            (exactRationalLiteral (-8948706130464933) 800000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-152985578403047491) 10240000000000000000),
            (exactRationalLiteral (-64701364346595711) 3200000000000000000),
            (exactRationalLiteral (1616548331779311) 40000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (13669345225326118337) 307200000000000000000),
            (exactRationalLiteral (710811262528760991) 6400000000000000000),
            (exactRationalLiteral (-4087241921753843) 80000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2873424577124329799) 409600000000000000000),
            (exactRationalLiteral (-5070051748240046067) 25600000000000000000),
            (exactRationalLiteral (-25241810710648197) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-17055921952113856081) 307200000000000000000),
            (exactRationalLiteral (166649472809922897) 1280000000000000000),
            (exactRationalLiteral (34626151626925799) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (37146076378202288809) 1228800000000000000000),
            (exactRationalLiteral (-374127710562163201) 25600000000000000000),
            (exactRationalLiteral (-108558818751505511) 1600000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (74120161364738973) 40960000000000000000),
            (exactRationalLiteral (-24706720454912991) 2560000000000000000),
            (exactRationalLiteral (2745191161656999) 160000000000000000),
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
          (exactRationalLiteral (15527045342269299) 800000000000000000),
          (exactRationalLiteral (2560252551045139) 50000000000000000),
          (exactRationalLiteral (9619210622189731) 600000000000000000),
          (exactRationalLiteral (431906134484819) 240000000000000000),
          (exactRationalLiteral (3943204762238119) 2400000000000000000),
          (exactRationalLiteral (1698624044589917) 2400000000000000000),
          (exactRationalLiteral (6214262043337927) 2400000000000000000),
          (exactRationalLiteral (98620359819877) 50000000000000000),
          (exactRationalLiteral (6973828138012493) 600000000000000000),
          (exactRationalLiteral (320134929331193929) 76800000000000000000),
          (exactRationalLiteral (651984026313443) 600000000000000000),
          (exactRationalLiteral (620371756545087253) 76800000000000000000),
          (exactRationalLiteral (786774271931907167) 30720000000000000000),
          (exactRationalLiteral (56830947744511799) 1200000000000000000),
          (exactRationalLiteral (11519951570718744967) 38400000000000000000),
          (exactRationalLiteral (60100417416640294271) 153600000000000000000),
          (exactRationalLiteral (3064010506321480789) 38400000000000000000),
          (exactRationalLiteral (6475943120289073) 2400000000000000000),
          (exactRationalLiteral (54155544075560535427) 153600000000000000000),
          (exactRationalLiteral (18859800609356117433) 25600000000000000000),
          (exactRationalLiteral (54155544075560535427) 153600000000000000000),
          (exactRationalLiteral (6475943120289073) 2400000000000000000),
          (exactRationalLiteral (3064010506321480789) 38400000000000000000),
          (exactRationalLiteral (60100417416640294271) 153600000000000000000),
          (exactRationalLiteral (11519951570718744967) 38400000000000000000),
          (exactRationalLiteral (56830947744511799) 1200000000000000000),
          (exactRationalLiteral (786774271931907167) 30720000000000000000),
          (exactRationalLiteral (620371756545087253) 76800000000000000000),
          (exactRationalLiteral (651984026313443) 600000000000000000),
          (exactRationalLiteral (320134929331193929) 76800000000000000000),
          (exactRationalLiteral (6973828138012493) 600000000000000000),
          (exactRationalLiteral (98620359819877) 50000000000000000),
          (exactRationalLiteral (6214262043337927) 2400000000000000000),
          (exactRationalLiteral (1698624044589917) 2400000000000000000),
          (exactRationalLiteral (3943204762238119) 2400000000000000000),
          (exactRationalLiteral (431906134484819) 240000000000000000),
          (exactRationalLiteral (9619210622189731) 600000000000000000),
          (exactRationalLiteral (2560252551045139) 50000000000000000),
          (exactRationalLiteral (15527045342269299) 800000000000000000),
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
      (37, 16),
      (37, 24)
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
            (exactRationalLiteral (34874095127716691) 40960000000000000000),
            (exactRationalLiteral (-14946040769021439) 2560000000000000000),
            (exactRationalLiteral (2135148681288777) 160000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (33743142158188607047) 1228800000000000000000),
            (exactRationalLiteral (-736094051379503457) 25600000000000000000),
            (exactRationalLiteral (-72424351657164617) 1600000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-11728943347608485143) 307200000000000000000),
            (exactRationalLiteral (927742270899604901) 6400000000000000000),
            (exactRationalLiteral (12621301798069409) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-12963527949781870921) 409600000000000000000),
            (exactRationalLiteral (-988913588216984631) 5120000000000000000),
            (exactRationalLiteral (87983714288209653) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (17606748601475376511) 307200000000000000000),
            (exactRationalLiteral (117590316446929107) 1280000000000000000),
            (exactRationalLiteral (-40993630538288513) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-513805192718523679) 30720000000000000000),
            (exactRationalLiteral (-23883898398054703) 3200000000000000000),
            (exactRationalLiteral (12325991315373949) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (1119090617742597061) 614400000000000000000),
            (exactRationalLiteral (-8031981616759891) 12800000000000000000),
            (exactRationalLiteral (-13213002098603051) 800000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2090544127320191081) 1228800000000000000000),
            (exactRationalLiteral (-18319912123241521) 25600000000000000000),
            (exactRationalLiteral (5901685931252167) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (907849560811863337) 1228800000000000000000),
            (exactRationalLiteral (10782196559054721) 25600000000000000000),
            (exactRationalLiteral (-2056356976326119) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1083951285033864379) 409600000000000000000),
            (exactRationalLiteral (24634187015354297) 25600000000000000000),
            (exactRationalLiteral (1311801504163713) 1600000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1282369912911144227) 614400000000000000000),
            (exactRationalLiteral (23458749224548419) 12800000000000000000),
            (exactRationalLiteral (-13366168253177) 160000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-907454068337410421) 76800000000000000000),
            (exactRationalLiteral (-4973807143251227) 1600000000000000000),
            (exactRationalLiteral (-36666249148289) 100000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-2552802071105232359) 614400000000000000000),
            (exactRationalLiteral (-2456753095134439) 12800000000000000000),
            (exactRationalLiteral (-1240910078509991) 800000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (274875970694754617) 204800000000000000000),
            (exactRationalLiteral (52453377579786651) 12800000000000000000),
            (exactRationalLiteral (28403070733071) 160000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4043490400456614743) 614400000000000000000),
            (exactRationalLiteral (99574211475274977) 12800000000000000000),
            (exactRationalLiteral (-831550544409767) 800000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-24956602457804399969) 1228800000000000000000),
            (exactRationalLiteral (677929278270242103) 25600000000000000000),
            (exactRationalLiteral (-16534182546699377) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (9953840809732728021) 204800000000000000000),
            (exactRationalLiteral (5243559404140063) 512000000000000000),
            (exactRationalLiteral (-116886429688951473) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (2468915708072448833) 12288000000000000000),
            (exactRationalLiteral (-2518560890628442247) 6400000000000000000),
            (exactRationalLiteral (254031814646610521) 400000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-310686711445651836373) 1228800000000000000000),
            (exactRationalLiteral (14348726625785529587) 25600000000000000000),
            (exactRationalLiteral (-1346624172309025669) 1600000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (6364186705886555147) 307200000000000000000),
            (exactRationalLiteral (-1433519985806944213) 6400000000000000000),
            (exactRationalLiteral (6860736653574851) 16000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (1439886843790440349) 409600000000000000000),
            (exactRationalLiteral (9802404793895143) 1024000000000000000),
            (exactRationalLiteral (-85103600280047097) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-382950709935983181377) 1228800000000000000000),
            (exactRationalLiteral (5117472209429807847) 25600000000000000000),
            (exactRationalLiteral (-146200035688924721) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (134178573403977498867) 204800000000000000000),
            (exactRationalLiteral (-5152135287290917839) 12800000000000000000),
            (exactRationalLiteral (25970909439630837) 160000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-382950709935983181377) 1228800000000000000000),
            (exactRationalLiteral (5117472209429807847) 25600000000000000000),
            (exactRationalLiteral (-146200035688924721) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (1439886843790440349) 409600000000000000000),
            (exactRationalLiteral (9802404793895143) 1024000000000000000),
            (exactRationalLiteral (-85103600280047097) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (6364186705886555147) 307200000000000000000),
            (exactRationalLiteral (-1433519985806944213) 6400000000000000000),
            (exactRationalLiteral (6860736653574851) 16000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-310686711445651836373) 1228800000000000000000),
            (exactRationalLiteral (14348726625785529587) 25600000000000000000),
            (exactRationalLiteral (-1346624172309025669) 1600000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (2468915708072448833) 12288000000000000000),
            (exactRationalLiteral (-2518560890628442247) 6400000000000000000),
            (exactRationalLiteral (254031814646610521) 400000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (9953840809732728021) 204800000000000000000),
            (exactRationalLiteral (5243559404140063) 512000000000000000),
            (exactRationalLiteral (-116886429688951473) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-24956602457804399969) 1228800000000000000000),
            (exactRationalLiteral (677929278270242103) 25600000000000000000),
            (exactRationalLiteral (-16534182546699377) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-4043490400456614743) 614400000000000000000),
            (exactRationalLiteral (99574211475274977) 12800000000000000000),
            (exactRationalLiteral (-831550544409767) 800000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (274875970694754617) 204800000000000000000),
            (exactRationalLiteral (52453377579786651) 12800000000000000000),
            (exactRationalLiteral (28403070733071) 160000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2552802071105232359) 614400000000000000000),
            (exactRationalLiteral (-2456753095134439) 12800000000000000000),
            (exactRationalLiteral (-1240910078509991) 800000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-907454068337410421) 76800000000000000000),
            (exactRationalLiteral (-4973807143251227) 1600000000000000000),
            (exactRationalLiteral (-36666249148289) 100000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (1282369912911144227) 614400000000000000000),
            (exactRationalLiteral (23458749224548419) 12800000000000000000),
            (exactRationalLiteral (-13366168253177) 160000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (1083951285033864379) 409600000000000000000),
            (exactRationalLiteral (24634187015354297) 25600000000000000000),
            (exactRationalLiteral (1311801504163713) 1600000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (907849560811863337) 1228800000000000000000),
            (exactRationalLiteral (10782196559054721) 25600000000000000000),
            (exactRationalLiteral (-2056356976326119) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-2090544127320191081) 1228800000000000000000),
            (exactRationalLiteral (-18319912123241521) 25600000000000000000),
            (exactRationalLiteral (5901685931252167) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (1119090617742597061) 614400000000000000000),
            (exactRationalLiteral (-8031981616759891) 12800000000000000000),
            (exactRationalLiteral (-13213002098603051) 800000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-513805192718523679) 30720000000000000000),
            (exactRationalLiteral (-23883898398054703) 3200000000000000000),
            (exactRationalLiteral (12325991315373949) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (17606748601475376511) 307200000000000000000),
            (exactRationalLiteral (117590316446929107) 1280000000000000000),
            (exactRationalLiteral (-40993630538288513) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-12963527949781870921) 409600000000000000000),
            (exactRationalLiteral (-988913588216984631) 5120000000000000000),
            (exactRationalLiteral (87983714288209653) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-11728943347608485143) 307200000000000000000),
            (exactRationalLiteral (927742270899604901) 6400000000000000000),
            (exactRationalLiteral (12621301798069409) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (33743142158188607047) 1228800000000000000000),
            (exactRationalLiteral (-736094051379503457) 25600000000000000000),
            (exactRationalLiteral (-72424351657164617) 1600000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (34874095127716691) 40960000000000000000),
            (exactRationalLiteral (-14946040769021439) 2560000000000000000),
            (exactRationalLiteral (2135148681288777) 160000000000000000),
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
          (exactRationalLiteral (2225155156968180181) 51200000000000000000),
          (exactRationalLiteral (2404667968262460991) 38400000000000000000),
          (exactRationalLiteral (54319947461130953) 3200000000000000000),
          (exactRationalLiteral (2964071493421591) 1600000000000000000),
          (exactRationalLiteral (265844662598369029) 153600000000000000000),
          (exactRationalLiteral (116708183616966557) 153600000000000000000),
          (exactRationalLiteral (416234544129893741) 153600000000000000000),
          (exactRationalLiteral (169061482413505571) 76800000000000000000),
          (exactRationalLiteral (19218294427168989) 1600000000000000000),
          (exactRationalLiteral (320501310498267191) 76800000000000000000),
          (exactRationalLiteral (4912381366727771) 3072000000000000000),
          (exactRationalLiteral (2828606563943157) 400000000000000000),
          (exactRationalLiteral (52810068625084627) 2400000000000000000),
          (exactRationalLiteral (188058418152249083) 3840000000000000000),
          (exactRationalLiteral (68432035768554923) 300000000000000000),
          (exactRationalLiteral (699109075468845169) 2400000000000000000),
          (exactRationalLiteral (273488472822671) 7500000000000000),
          (exactRationalLiteral (601627072934294267) 153600000000000000000),
          (exactRationalLiteral (259604446661511263) 800000000000000000),
          (exactRationalLiteral (817167956189846509) 1200000000000000000),
          (exactRationalLiteral (259604446661511263) 800000000000000000),
          (exactRationalLiteral (601627072934294267) 153600000000000000000),
          (exactRationalLiteral (273488472822671) 7500000000000000),
          (exactRationalLiteral (699109075468845169) 2400000000000000000),
          (exactRationalLiteral (68432035768554923) 300000000000000000),
          (exactRationalLiteral (188058418152249083) 3840000000000000000),
          (exactRationalLiteral (52810068625084627) 2400000000000000000),
          (exactRationalLiteral (2828606563943157) 400000000000000000),
          (exactRationalLiteral (4912381366727771) 3072000000000000000),
          (exactRationalLiteral (320501310498267191) 76800000000000000000),
          (exactRationalLiteral (19218294427168989) 1600000000000000000),
          (exactRationalLiteral (169061482413505571) 76800000000000000000),
          (exactRationalLiteral (416234544129893741) 153600000000000000000),
          (exactRationalLiteral (116708183616966557) 153600000000000000000),
          (exactRationalLiteral (265844662598369029) 153600000000000000000),
          (exactRationalLiteral (2964071493421591) 1600000000000000000),
          (exactRationalLiteral (54319947461130953) 3200000000000000000),
          (exactRationalLiteral (2404667968262460991) 38400000000000000000),
          (exactRationalLiteral (2225155156968180181) 51200000000000000000),
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
      (37, 15),
      (37, 23)
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
            (exactRationalLiteral (101673746728037) 327680000000000000),
            (exactRationalLiteral (-305021240184111) 102400000000000000),
            (exactRationalLiteral (305021240184111) 32000000000000000),
            (exactRationalLiteral (-101673746728037) 10000000000000000)
          ],
          ![
            (exactRationalLiteral (28602023498402974477) 1228800000000000000000),
            (exactRationalLiteral (-953522523819480137) 25600000000000000000),
            (exactRationalLiteral (-36289884562823723) 1600000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-6099053499949448389) 307200000000000000000),
            (exactRationalLiteral (934217778434169757) 6400000000000000000),
            (exactRationalLiteral (-9383548030786981) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (-22349761608133734819) 409600000000000000000),
            (exactRationalLiteral (-4366182033934368843) 25600000000000000000),
            (exactRationalLiteral (201209239287067503) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (6853434948235236791) 102400000000000000000),
            (exactRationalLiteral (382862218222452887) 6400000000000000000),
            (exactRationalLiteral (-61551051467807811) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-2547444459570549649) 153600000000000000000),
            (exactRationalLiteral (33906566176395881) 3200000000000000000),
            (exactRationalLiteral (16569240971851343) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (895285518986248631) 614400000000000000000),
            (exactRationalLiteral (-69412581947448331) 12800000000000000000),
            (exactRationalLiteral (-17477298066741169) 800000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-424262265602191783) 245760000000000000000),
            (exactRationalLiteral (9452852038594791) 25600000000000000000),
            (exactRationalLiteral (7984696149665989) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (944973571455744739) 1228800000000000000000),
            (exactRationalLiteral (1110326156483497) 25600000000000000000),
            (exactRationalLiteral (-2779578224959493) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (3416876854275705563) 1228800000000000000000),
            (exactRationalLiteral (30619522548020193) 25600000000000000000),
            (exactRationalLiteral (336173252433847) 320000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (473963322713222011) 204800000000000000000),
            (exactRationalLiteral (4595238169539167) 2560000000000000000),
            (exactRationalLiteral (-174448347160407) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-37507122324108691) 3072000000000000000),
            (exactRationalLiteral (-1018209619570879) 320000000000000000),
            (exactRationalLiteral (-4390845630659) 20000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (-861118965832644639) 204800000000000000000),
            (exactRationalLiteral (-7882086849061919) 12800000000000000000),
            (exactRationalLiteral (-1471756798453749) 800000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (228309964298888533) 122880000000000000000),
            (exactRationalLiteral (10654033767637079) 2560000000000000000),
            (exactRationalLiteral (266380275534017) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-1151922590843240223) 204800000000000000000),
            (exactRationalLiteral (96375992101716617) 12800000000000000000),
            (exactRationalLiteral (-767559142369413) 800000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4219467722487700591) 245760000000000000000),
            (exactRationalLiteral (121368346247172611) 5120000000000000000),
            (exactRationalLiteral (-19009590970490147) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (5881325340119609297) 122880000000000000000),
            (exactRationalLiteral (-255852975129168993) 12800000000000000000),
            (exactRationalLiteral (-76584550427383811) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (49390038658888997411) 307200000000000000000),
            (exactRationalLiteral (-327473773899489651) 1280000000000000000),
            (exactRationalLiteral (7462567836755459) 16000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-239385179357741171783) 1228800000000000000000),
            (exactRationalLiteral (9646561137002324459) 25600000000000000000),
            (exactRationalLiteral (-200891714416515379) 320000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (-360999688811475223) 307200000000000000000),
            (exactRationalLiteral (-838590058413869309) 6400000000000000000),
            (exactRationalLiteral (125946547357166177) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (4876669994303336573) 1228800000000000000000),
            (exactRationalLiteral (-41408307668655193) 25600000000000000000),
            (exactRationalLiteral (-58130613477969787) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-117971549967245354617) 409600000000000000000),
            (exactRationalLiteral (4575485669641792511) 25600000000000000000),
            (exactRationalLiteral (-124793234205082947) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (373114732224151240307) 614400000000000000000),
            (exactRationalLiteral (-4665932513705100839) 12800000000000000000),
            (exactRationalLiteral (22649367918950863) 160000000000000000),
            (exactRationalLiteral (-1660770760339987) 30000000000000000)
          ],
          ![
            (exactRationalLiteral (-117971549967245354617) 409600000000000000000),
            (exactRationalLiteral (4575485669641792511) 25600000000000000000),
            (exactRationalLiteral (-124793234205082947) 1600000000000000000),
            (exactRationalLiteral (10703400741920887) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (4876669994303336573) 1228800000000000000000),
            (exactRationalLiteral (-41408307668655193) 25600000000000000000),
            (exactRationalLiteral (-58130613477969787) 1600000000000000000),
            (exactRationalLiteral (2697298680207731) 60000000000000000)
          ],
          ![
            (exactRationalLiteral (-360999688811475223) 307200000000000000000),
            (exactRationalLiteral (-838590058413869309) 6400000000000000000),
            (exactRationalLiteral (125946547357166177) 400000000000000000),
            (exactRationalLiteral (-7595311497034183) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (-239385179357741171783) 1228800000000000000000),
            (exactRationalLiteral (9646561137002324459) 25600000000000000000),
            (exactRationalLiteral (-200891714416515379) 320000000000000000),
            (exactRationalLiteral (171082800113224387) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (49390038658888997411) 307200000000000000000),
            (exactRationalLiteral (-327473773899489651) 1280000000000000000),
            (exactRationalLiteral (7462567836755459) 16000000000000000),
            (exactRationalLiteral (-11244603121287341) 25000000000000000)
          ],
          ![
            (exactRationalLiteral (5881325340119609297) 122880000000000000000),
            (exactRationalLiteral (-255852975129168993) 12800000000000000000),
            (exactRationalLiteral (-76584550427383811) 800000000000000000),
            (exactRationalLiteral (20150939630783831) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-4219467722487700591) 245760000000000000000),
            (exactRationalLiteral (121368346247172611) 5120000000000000000),
            (exactRationalLiteral (-19009590970490147) 1600000000000000000),
            (exactRationalLiteral (-82513614126359) 20000000000000000)
          ],
          ![
            (exactRationalLiteral (-1151922590843240223) 204800000000000000000),
            (exactRationalLiteral (96375992101716617) 12800000000000000000),
            (exactRationalLiteral (-767559142369413) 800000000000000000),
            (exactRationalLiteral (31995701020177) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (228309964298888533) 122880000000000000000),
            (exactRationalLiteral (10654033767637079) 2560000000000000000),
            (exactRationalLiteral (266380275534017) 800000000000000000),
            (exactRationalLiteral (62182460934331) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-861118965832644639) 204800000000000000000),
            (exactRationalLiteral (-7882086849061919) 12800000000000000000),
            (exactRationalLiteral (-1471756798453749) 800000000000000000),
            (exactRationalLiteral (-115423359971879) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-37507122324108691) 3072000000000000000),
            (exactRationalLiteral (-1018209619570879) 320000000000000000),
            (exactRationalLiteral (-4390845630659) 20000000000000000),
            (exactRationalLiteral (7356010497497) 18750000000000000)
          ],
          ![
            (exactRationalLiteral (473963322713222011) 204800000000000000000),
            (exactRationalLiteral (4595238169539167) 2560000000000000000),
            (exactRationalLiteral (-174448347160407) 800000000000000000),
            (exactRationalLiteral (-53808752947261) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (3416876854275705563) 1228800000000000000000),
            (exactRationalLiteral (30619522548020193) 25600000000000000000),
            (exactRationalLiteral (336173252433847) 320000000000000000),
            (exactRationalLiteral (184532379002761) 300000000000000000)
          ],
          ![
            (exactRationalLiteral (944973571455744739) 1228800000000000000000),
            (exactRationalLiteral (1110326156483497) 25600000000000000000),
            (exactRationalLiteral (-2779578224959493) 1600000000000000000),
            (exactRationalLiteral (-120536874772229) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (-424262265602191783) 245760000000000000000),
            (exactRationalLiteral (9452852038594791) 25600000000000000000),
            (exactRationalLiteral (7984696149665989) 1600000000000000000),
            (exactRationalLiteral (347168369735637) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (895285518986248631) 614400000000000000000),
            (exactRationalLiteral (-69412581947448331) 12800000000000000000),
            (exactRationalLiteral (-17477298066741169) 800000000000000000),
            (exactRationalLiteral (-2132147984069059) 150000000000000000)
          ],
          ![
            (exactRationalLiteral (-2547444459570549649) 153600000000000000000),
            (exactRationalLiteral (33906566176395881) 3200000000000000000),
            (exactRationalLiteral (16569240971851343) 200000000000000000),
            (exactRationalLiteral (2121624828238697) 37500000000000000)
          ],
          ![
            (exactRationalLiteral (6853434948235236791) 102400000000000000000),
            (exactRationalLiteral (382862218222452887) 6400000000000000000),
            (exactRationalLiteral (-61551051467807811) 400000000000000000),
            (exactRationalLiteral (-10278710464759649) 75000000000000000)
          ],
          ![
            (exactRationalLiteral (-22349761608133734819) 409600000000000000000),
            (exactRationalLiteral (-4366182033934368843) 25600000000000000000),
            (exactRationalLiteral (201209239287067503) 1600000000000000000),
            (exactRationalLiteral (754836833325719) 4000000000000000)
          ],
          ![
            (exactRationalLiteral (-6099053499949448389) 307200000000000000000),
            (exactRationalLiteral (934217778434169757) 6400000000000000000),
            (exactRationalLiteral (-9383548030786981) 400000000000000000),
            (exactRationalLiteral (-733494994295213) 5000000000000000)
          ],
          ![
            (exactRationalLiteral (28602023498402974477) 1228800000000000000000),
            (exactRationalLiteral (-953522523819480137) 25600000000000000000),
            (exactRationalLiteral (-36289884562823723) 1600000000000000000),
            (exactRationalLiteral (6022411182390149) 100000000000000000)
          ],
          ![
            (exactRationalLiteral (101673746728037) 327680000000000000),
            (exactRationalLiteral (-305021240184111) 102400000000000000),
            (exactRationalLiteral (305021240184111) 32000000000000000),
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
          (exactRationalLiteral (413997866905435831) 6400000000000000000),
          (exactRationalLiteral (336155619289138843) 4800000000000000000),
          (exactRationalLiteral (21679817166770183) 1280000000000000000),
          (exactRationalLiteral (43884313275518299) 25600000000000000000),
          (exactRationalLiteral (44535570231041933) 25600000000000000000),
          (exactRationalLiteral (29663283951922013) 38400000000000000000),
          (exactRationalLiteral (18301888297319149) 6400000000000000000),
          (exactRationalLiteral (23285021670130079) 9600000000000000000),
          (exactRationalLiteral (29781553408445089) 2400000000000000000),
          (exactRationalLiteral (1632208657375283) 384000000000000000),
          (exactRationalLiteral (6782404433836121) 3200000000000000000),
          (exactRationalLiteral (468403802745374867) 76800000000000000000),
          (exactRationalLiteral (2871706859355708397) 153600000000000000000),
          (exactRationalLiteral (149621405175363091) 3072000000000000000),
          (exactRationalLiteral (6861946458062732953) 38400000000000000000),
          (exactRationalLiteral (11312888386879545843) 51200000000000000000),
          (exactRationalLiteral (319424507874091723) 38400000000000000000),
          (exactRationalLiteral (311855963053187513) 76800000000000000000),
          (exactRationalLiteral (46003273751752326389) 153600000000000000000),
          (exactRationalLiteral (48432571767231563213) 76800000000000000000),
          (exactRationalLiteral (46003273751752326389) 153600000000000000000),
          (exactRationalLiteral (311855963053187513) 76800000000000000000),
          (exactRationalLiteral (319424507874091723) 38400000000000000000),
          (exactRationalLiteral (11312888386879545843) 51200000000000000000),
          (exactRationalLiteral (6861946458062732953) 38400000000000000000),
          (exactRationalLiteral (149621405175363091) 3072000000000000000),
          (exactRationalLiteral (2871706859355708397) 153600000000000000000),
          (exactRationalLiteral (468403802745374867) 76800000000000000000),
          (exactRationalLiteral (6782404433836121) 3200000000000000000),
          (exactRationalLiteral (1632208657375283) 384000000000000000),
          (exactRationalLiteral (29781553408445089) 2400000000000000000),
          (exactRationalLiteral (23285021670130079) 9600000000000000000),
          (exactRationalLiteral (18301888297319149) 6400000000000000000),
          (exactRationalLiteral (29663283951922013) 38400000000000000000),
          (exactRationalLiteral (44535570231041933) 25600000000000000000),
          (exactRationalLiteral (43884313275518299) 25600000000000000000),
          (exactRationalLiteral (21679817166770183) 1280000000000000000),
          (exactRationalLiteral (336155619289138843) 4800000000000000000),
          (exactRationalLiteral (413997866905435831) 6400000000000000000),
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
      (37, 14),
      (37, 22)
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
theorem generatorCoordinates22_valid : ∀ i, (generatorCoordinates22 i).IsValid := by
  unfold GeneratorCoordinateData.IsValid GeneratorCubicIntervalData.IsValid
  decide +kernel

end PartialBalayage.Maximal.Square
