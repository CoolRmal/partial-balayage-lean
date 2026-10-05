/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.PowerEnclosure

/-!
# Exact radial fifth-root data for all majorization triangles

Each literal row is checked by ordinary rational arithmetic in Lean. The data generator
is outside the trusted proof: validity follows from the explicit fifth-power inequalities,
and the real fractional-power bounds follow from `IsPowerEnclosure.rpow_bounds`.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- One exact radial enclosure row, at an actual positive triangle maximum radius. -/
structure RadialPowerData where
  radius : ℚ
  lowerSix : ℚ
  upperSix : ℚ
  lowerEleven : ℚ
  upperEleven : ℚ
  deriving DecidableEq

/-- The ordinary rational checks required for one actual radial enclosure row. -/
def RadialPowerData.IsValid (t : RadialPowerData) : Prop :=
  0 < t.radius ∧ IsPowerEnclosure t.radius (-6) t.lowerSix t.upperSix ∧
    IsPowerEnclosure t.radius (-11) t.lowerEleven t.upperEleven

/-- Literal radial enclosure row 1 of 33. -/
def radialPowerData0 : RadialPowerData where
  radius := 1 / 16
  lowerSix := 35313726210923359253896589521535 / 1267650600228229401496703205376
  upperSix := 275888486022838744171067105637 / 9903520314283042199192993792
  lowerEleven := 282509809687386874031172716172285 / 633825300114114700748351602688
  upperEleven := 565019619374773748062345432344571 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 1. -/
theorem radialPowerData0_valid : radialPowerData0.IsValid := by
  norm_num [radialPowerData0, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 2 of 33. -/
def radialPowerData1 : RadialPowerData where
  radius := 1 / 8
  lowerSix := 15371192122502216961117275096919 / 1267650600228229401496703205376
  upperSix := 1921399015312777120139659387115 / 158456325028528675187087900672
  lowerEleven := 15371192122502216961117275096919 / 158456325028528675187087900672
  upperEleven := 122969536980017735688938200775353 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 2. -/
theorem radialPowerData1_valid : radialPowerData1.IsValid := by
  norm_num [radialPowerData1, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 3 of 33. -/
def radialPowerData2 : RadialPowerData where
  radius := 3 / 16
  lowerSix := 590579077711037725489355747317 / 79228162514264337593543950336
  upperSix := 9449265243376603607829691957073 / 1267650600228229401496703205376
  lowerEleven := 25198040649004276287545845218859 / 633825300114114700748351602688
  upperEleven := 50396081298008552575091690437719 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 3. -/
theorem radialPowerData2_valid : radialPowerData2.IsValid := by
  norm_num [radialPowerData2, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 4 of 33. -/
def radialPowerData3 : RadialPowerData where
  radius := 1 / 4
  lowerSix := 3345349990194312744755744271767 / 633825300114114700748351602688
  upperSix := 6690699980388625489511488543535 / 1267650600228229401496703205376
  lowerEleven := 26762799921554501958045954174137 / 1267650600228229401496703205376
  upperEleven := 13381399960777250979022977087069 / 633825300114114700748351602688

/-- Exact rational fifth-power checks for radial row 4. -/
theorem radialPowerData3_valid : radialPowerData3.IsValid := by
  norm_num [radialPowerData3, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 5 of 33. -/
def radialPowerData4 : RadialPowerData where
  radius := 5 / 16
  lowerSix := 1279733530317962684579327975915 / 316912650057057350374175801344
  upperSix := 5118934121271850738317311903661 / 1267650600228229401496703205376
  lowerEleven := 255946706063592536915865595183 / 19807040628566084398385987584
  upperEleven := 16380589188069922362615398091713 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 5. -/
theorem radialPowerData4_valid : radialPowerData4.IsValid := by
  norm_num [radialPowerData4, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 6 of 33. -/
def radialPowerData5 : RadialPowerData where
  radius := 3 / 8
  lowerSix := 257064474386124682109035727417 / 79228162514264337593543950336
  upperSix := 4113031590177994913744571638673 / 1267650600228229401496703205376
  lowerEleven := 10968084240474653103318857703125 / 1267650600228229401496703205376
  upperEleven := 5484042120237326551659428851563 / 633825300114114700748351602688

/-- Exact rational fifth-power checks for radial row 6. -/
theorem radialPowerData5_valid : radialPowerData5.IsValid := by
  norm_num [radialPowerData5, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 7 of 33. -/
def radialPowerData6 : RadialPowerData where
  radius := 7 / 16
  lowerSix := 53412871145889023724664684087 / 19807040628566084398385987584
  upperSix := 3418423753336897518378539781569 / 1267650600228229401496703205376
  lowerEleven := 3906770003813597163861188321793 / 633825300114114700748351602688
  upperEleven := 7813540007627194327722376643587 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 7. -/
theorem radialPowerData6_valid : radialPowerData6.IsValid := by
  norm_num [radialPowerData6, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 8 of 33. -/
def radialPowerData7 : RadialPowerData where
  radius := 1 / 2
  lowerSix := 728074079596585581325252169787 / 316912650057057350374175801344
  upperSix := 2912296318386342325301008679149 / 1267650600228229401496703205376
  lowerEleven := 728074079596585581325252169787 / 158456325028528675187087900672
  upperEleven := 5824592636772684650602017358297 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 8. -/
theorem radialPowerData7_valid : radialPowerData7.IsValid := by
  norm_num [radialPowerData7, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 9 of 33. -/
def radialPowerData8 : RadialPowerData where
  radius := 9 / 16
  lowerSix := 2528439312984933684099270765215 / 1267650600228229401496703205376
  upperSix := 79013728530779177628102211413 / 39614081257132168796771975168
  lowerEleven := 1123750805771081637377453673429 / 316912650057057350374175801344
  upperEleven := 4495003223084326549509814693717 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 9. -/
theorem radialPowerData8_valid : radialPowerData8.IsValid := by
  norm_num [radialPowerData8, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 10 of 33. -/
def radialPowerData9 : RadialPowerData where
  radius := 5 / 8
  lowerSix := 1114072745687239974062751794345 / 633825300114114700748351602688
  upperSix := 2228145491374479948125503588691 / 1267650600228229401496703205376
  lowerEleven := 3565032786199167917000805741905 / 1267650600228229401496703205376
  upperEleven := 1782516393099583958500402870953 / 633825300114114700748351602688

/-- Exact rational fifth-power checks for radial row 10. -/
theorem radialPowerData9_valid : radialPowerData9.IsValid := by
  norm_num [radialPowerData9, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 11 of 33. -/
def radialPowerData10 : RadialPowerData where
  radius := 11 / 16
  lowerSix := 993670342162085384707594104333 / 633825300114114700748351602688
  upperSix := 1987340684324170769415188208667 / 1267650600228229401496703205376
  lowerEleven := 90333667469280489518872191303 / 39614081257132168796771975168
  upperEleven := 2890677359016975664603910121697 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 11. -/
theorem radialPowerData10_valid : radialPowerData10.IsValid := by
  norm_num [radialPowerData10, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 12 of 33. -/
def radialPowerData11 : RadialPowerData where
  radius := 3 / 4
  lowerSix := 1790300983842103340626607882753 / 1267650600228229401496703205376
  upperSix := 895150491921051670313303941377 / 633825300114114700748351602688
  lowerEleven := 2387067978456137787502143843671 / 1267650600228229401496703205376
  upperEleven := 298383497307017223437767980459 / 158456325028528675187087900672

/-- Exact rational fifth-power checks for radial row 12. -/
theorem radialPowerData11_valid : radialPowerData11.IsValid := by
  norm_num [radialPowerData11, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 13 of 33. -/
def radialPowerData12 : RadialPowerData where
  radius := 13 / 16
  lowerSix := 1626340670945419297927804046605 / 1267650600228229401496703205376
  upperSix := 813170335472709648963902023303 / 633825300114114700748351602688
  lowerEleven := 1000825028274104183340187105603 / 633825300114114700748351602688
  upperEleven := 2001650056548208366680374211207 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 13. -/
theorem radialPowerData12_valid : radialPowerData12.IsValid := by
  norm_num [radialPowerData12, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 14 of 33. -/
def radialPowerData13 : RadialPowerData where
  radius := 7 / 8
  lowerSix := 371988840506535881807200809143 / 316912650057057350374175801344
  upperSix := 1487955362026143527228803236573 / 1267650600228229401496703205376
  lowerEleven := 53141262929505125972457258449 / 39614081257132168796771975168
  upperEleven := 1700520413744164031118632270369 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 14. -/
theorem radialPowerData13_valid : radialPowerData13.IsValid := by
  norm_num [radialPowerData13, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 15 of 33. -/
def radialPowerData14 : RadialPowerData where
  radius := 15 / 16
  lowerSix := 171215882127395814402107410865 / 158456325028528675187087900672
  upperSix := 1369727057019166515216859286921 / 1267650600228229401496703205376
  lowerEleven := 1461042194153777616231316572715 / 1267650600228229401496703205376
  upperEleven := 365260548538444404057829143179 / 316912650057057350374175801344

/-- Exact rational fifth-power checks for radial row 15. -/
theorem radialPowerData14_valid : radialPowerData14.IsValid := by
  norm_num [radialPowerData14, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 16 of 33. -/
def radialPowerData15 : RadialPowerData where
  radius := 1
  lowerSix := 1
  upperSix := 1267650600228229401496703205377 / 1267650600228229401496703205376
  lowerEleven := 1
  upperEleven := 1267650600228229401496703205377 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 16. -/
theorem radialPowerData15_valid : radialPowerData15.IsValid := by
  norm_num [radialPowerData15, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 17 of 33. -/
def radialPowerData16 : RadialPowerData where
  radius := 17 / 16
  lowerSix := 1178704224165504420932954633795 / 1267650600228229401496703205376
  upperSix := 294676056041376105233238658449 / 316912650057057350374175801344
  lowerEleven := 1109368681567533572642780831807 / 1267650600228229401496703205376
  upperEleven := 17333885649492712072543450497 / 19807040628566084398385987584

/-- Exact rational fifth-power checks for radial row 17. -/
theorem radialPowerData16_valid : radialPowerData16.IsValid := by
  norm_num [radialPowerData16, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 18 of 33. -/
def radialPowerData17 : RadialPowerData where
  radius := 9 / 8
  lowerSix := 550283567044774786031562447275 / 633825300114114700748351602688
  upperSix := 1100567134089549572063124894551 / 1267650600228229401496703205376
  lowerEleven := 489140948484244254250277730911 / 633825300114114700748351602688
  upperEleven := 978281896968488508500555461823 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 18. -/
theorem radialPowerData17_valid : radialPowerData17.IsValid := by
  norm_num [radialPowerData17, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 19 of 33. -/
def radialPowerData18 : RadialPowerData where
  radius := 19 / 16
  lowerSix := 515714365140350337855338040435 / 633825300114114700748351602688
  upperSix := 1031428730280700675710676080871 / 1267650600228229401496703205376
  lowerEleven := 868571562341642674282674594417 / 1267650600228229401496703205376
  upperEleven := 434285781170821337141337297209 / 633825300114114700748351602688

/-- Exact rational fifth-power checks for radial row 19. -/
theorem radialPowerData18_valid : radialPowerData18.IsValid := by
  norm_num [radialPowerData18, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 20 of 33. -/
def radialPowerData19 : RadialPowerData where
  radius := 5 / 4
  lowerSix := 484928328155443207044124292515 / 633825300114114700748351602688
  upperSix := 969856656310886414088248585031 / 1267650600228229401496703205376
  lowerEleven := 96985665631088641408824858503 / 158456325028528675187087900672
  upperEleven := 775885325048709131270598868025 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 20. -/
theorem radialPowerData19_valid : radialPowerData19.IsValid := by
  norm_num [radialPowerData19, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 21 of 33. -/
def radialPowerData20 : RadialPowerData where
  radius := 21 / 16
  lowerSix := 914703607503976898163284799609 / 1267650600228229401496703205376
  upperSix := 457351803751988449081642399805 / 633825300114114700748351602688
  lowerEleven := 43557314643046518960156419029 / 79228162514264337593543950336
  upperEleven := 696917034288744303362502704465 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 21. -/
theorem radialPowerData20_valid : radialPowerData20.IsValid := by
  norm_num [radialPowerData20, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 22 of 33. -/
def radialPowerData21 : RadialPowerData where
  radius := 11 / 8
  lowerSix := 865040276099855843569258045789 / 1267650600228229401496703205376
  upperSix := 432520138049927921784629022895 / 633825300114114700748351602688
  lowerEleven := 629120200799895158959460396937 / 1267650600228229401496703205376
  upperEleven := 314560100399947579479730198469 / 633825300114114700748351602688

/-- Exact rational fifth-power checks for radial row 22. -/
theorem radialPowerData21_valid : radialPowerData21.IsValid := by
  norm_num [radialPowerData21, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 23 of 33. -/
def radialPowerData22 : RadialPowerData where
  radius := 89 / 64
  lowerSix := 853389956184940119997794491829 / 1267650600228229401496703205376
  upperSix := 426694978092470059998897245915 / 633825300114114700748351602688
  lowerEleven := 76709209544713718651487145333 / 158456325028528675187087900672
  upperEleven := 613673676357709749211897162665 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 23. -/
theorem radialPowerData22_valid : radialPowerData22.IsValid := by
  norm_num [radialPowerData22, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 24 of 33. -/
def radialPowerData23 : RadialPowerData where
  radius := 179 / 128
  lowerSix := 847672107090101888557496302319 / 1267650600228229401496703205376
  upperSix := 52979506693131368034843518895 / 79228162514264337593543950336
  lowerEleven := 75769573818109666016312518643 / 158456325028528675187087900672
  upperEleven := 606156590544877328130500149145 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 24. -/
theorem radialPowerData23_valid : radialPowerData23.IsValid := by
  norm_num [radialPowerData23, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 25 of 33. -/
def radialPowerData24 : RadialPowerData where
  radius := 45 / 32
  lowerSix := 842024103898638051375726123741 / 1267650600228229401496703205376
  upperSix := 421012051949319025687863061871 / 633825300114114700748351602688
  lowerEleven := 598772696105698169867183021327 / 1267650600228229401496703205376
  upperEleven := 37423293506606135616698938833 / 79228162514264337593543950336

/-- Exact rational fifth-power checks for radial row 25. -/
theorem radialPowerData24_valid : radialPowerData24.IsValid := by
  norm_num [radialPowerData24, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 26 of 33. -/
def radialPowerData25 : RadialPowerData where
  radius := 91 / 64
  lowerSix := 207733181762499489360591109457 / 316912650057057350374175801344
  upperSix := 830932727049997957442364437829 / 1267650600228229401496703205376
  lowerEleven := 584392247595602959080344220011 / 1267650600228229401496703205376
  upperEleven := 146098061898900739770086055003 / 316912650057057350374175801344

/-- Exact rational fifth-power checks for radial row 26. -/
theorem radialPowerData25_valid : radialPowerData25.IsValid := by
  norm_num [radialPowerData25, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 27 of 33. -/
def radialPowerData26 : RadialPowerData where
  radius := 23 / 16
  lowerSix := 820106289113248795207506545789 / 1267650600228229401496703205376
  upperSix := 410053144556624397603753272895 / 633825300114114700748351602688
  lowerEleven := 570508722861390466231308901419 / 1267650600228229401496703205376
  upperEleven := 142627180715347616557827225355 / 316912650057057350374175801344

/-- Exact rational fifth-power checks for radial row 27. -/
theorem radialPowerData26_valid : radialPowerData26.IsValid := by
  norm_num [radialPowerData26, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 28 of 33. -/
def radialPowerData27 : RadialPowerData where
  radius := 47 / 32
  lowerSix := 799212211172829168178016492999 / 1267650600228229401496703205376
  upperSix := 99901526396603646022252061625 / 158456325028528675187087900672
  lowerEleven := 544144484202777305993543144169 / 1267650600228229401496703205376
  upperEleven := 272072242101388652996771572085 / 633825300114114700748351602688

/-- Exact rational fifth-power checks for radial row 28. -/
theorem radialPowerData27_valid : radialPowerData27.IsValid := by
  norm_num [radialPowerData27, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 29 of 33. -/
def radialPowerData28 : RadialPowerData where
  radius := 3 / 2
  lowerSix := 389636882488337075980433593791 / 633825300114114700748351602688
  upperSix := 779273764976674151960867187583 / 1267650600228229401496703205376
  lowerEleven := 129878960829445691993477864597 / 316912650057057350374175801344
  upperEleven := 519515843317782767973911458389 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 29. -/
theorem radialPowerData28_valid : radialPowerData28.IsValid := by
  norm_num [radialPowerData28, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 30 of 33. -/
def radialPowerData29 : RadialPowerData where
  radius := 25 / 16
  lowerSix := 742019870160738377876461971423 / 1267650600228229401496703205376
  upperSix := 23188120942523074308639436607 / 39614081257132168796771975168
  lowerEleven := 474892716902872561840935661711 / 1267650600228229401496703205376
  upperEleven := 29680794806429535115058478857 / 79228162514264337593543950336

/-- Exact rational fifth-power checks for radial row 30. -/
theorem radialPowerData29_valid : radialPowerData29.IsValid := by
  norm_num [radialPowerData29, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 31 of 33. -/
def radialPowerData30 : RadialPowerData where
  radius := 13 / 8
  lowerSix := 88488236700183202700508163961 / 158456325028528675187087900672
  upperSix := 707905893601465621604065311689 / 1267650600228229401496703205376
  lowerEleven := 217817198031220191262789326673 / 633825300114114700748351602688
  upperEleven := 435634396062440382525578653347 / 1267650600228229401496703205376

/-- Exact rational fifth-power checks for radial row 31. -/
theorem radialPowerData30_valid : radialPowerData30.IsValid := by
  norm_num [radialPowerData30, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 32 of 33. -/
def radialPowerData31 : RadialPowerData where
  radius := 27 / 16
  lowerSix := 676561107640496792867369161619 / 1267650600228229401496703205376
  upperSix := 169140276910124198216842290405 / 316912650057057350374175801344
  lowerEleven := 400925100823998099476959503181 / 1267650600228229401496703205376
  upperEleven := 200462550411999049738479751591 / 633825300114114700748351602688

/-- Exact rational fifth-power checks for radial row 32. -/
theorem radialPowerData31_valid : radialPowerData31.IsValid := by
  norm_num [radialPowerData31, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Literal radial enclosure row 33 of 33. -/
def radialPowerData32 : RadialPowerData where
  radius := 7 / 4
  lowerSix := 80958773660709223062564327381 / 158456325028528675187087900672
  upperSix := 647670189285673784500514619049 / 1267650600228229401496703205376
  lowerEleven := 370097251020385019714579782313 / 1267650600228229401496703205376
  upperEleven := 185048625510192509857289891157 / 633825300114114700748351602688

/-- Exact rational fifth-power checks for radial row 33. -/
theorem radialPowerData32_valid : radialPowerData32.IsValid := by
  norm_num [radialPowerData32, RadialPowerData.IsValid, IsPowerEnclosure]

/-- Every distinct actual maximum radius used by the majorization candidate. -/
def radialPowerData : List RadialPowerData := [
  radialPowerData0, radialPowerData1, radialPowerData2, radialPowerData3,
  radialPowerData4, radialPowerData5, radialPowerData6, radialPowerData7,
  radialPowerData8, radialPowerData9, radialPowerData10, radialPowerData11,
  radialPowerData12, radialPowerData13, radialPowerData14, radialPowerData15,
  radialPowerData16, radialPowerData17, radialPowerData18, radialPowerData19,
  radialPowerData20, radialPowerData21, radialPowerData22, radialPowerData23,
  radialPowerData24, radialPowerData25, radialPowerData26, radialPowerData27,
  radialPowerData28, radialPowerData29, radialPowerData30, radialPowerData31,
  radialPowerData32
]

/-- All 33 actual enclosure rows pass their exact rational predicates. -/
theorem radialPowerData_valid : ∀ t ∈ radialPowerData, t.IsValid := by
  intro t ht
  simp only [radialPowerData, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 |
    h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 |
    h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32
  · subst t
    exact radialPowerData0_valid
  · subst t
    exact radialPowerData1_valid
  · subst t
    exact radialPowerData2_valid
  · subst t
    exact radialPowerData3_valid
  · subst t
    exact radialPowerData4_valid
  · subst t
    exact radialPowerData5_valid
  · subst t
    exact radialPowerData6_valid
  · subst t
    exact radialPowerData7_valid
  · subst t
    exact radialPowerData8_valid
  · subst t
    exact radialPowerData9_valid
  · subst t
    exact radialPowerData10_valid
  · subst t
    exact radialPowerData11_valid
  · subst t
    exact radialPowerData12_valid
  · subst t
    exact radialPowerData13_valid
  · subst t
    exact radialPowerData14_valid
  · subst t
    exact radialPowerData15_valid
  · subst t
    exact radialPowerData16_valid
  · subst t
    exact radialPowerData17_valid
  · subst t
    exact radialPowerData18_valid
  · subst t
    exact radialPowerData19_valid
  · subst t
    exact radialPowerData20_valid
  · subst t
    exact radialPowerData21_valid
  · subst t
    exact radialPowerData22_valid
  · subst t
    exact radialPowerData23_valid
  · subst t
    exact radialPowerData24_valid
  · subst t
    exact radialPowerData25_valid
  · subst t
    exact radialPowerData26_valid
  · subst t
    exact radialPowerData27_valid
  · subst t
    exact radialPowerData28_valid
  · subst t
    exact radialPowerData29_valid
  · subst t
    exact radialPowerData30_valid
  · subst t
    exact radialPowerData31_valid
  · subst t
    exact radialPowerData32_valid

end PartialBalayage.Maximal.Square
