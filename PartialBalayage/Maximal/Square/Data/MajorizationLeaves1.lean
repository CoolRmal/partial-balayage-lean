/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices1

/-!
# Ordinary kernel checks of actual majorization leaves

Each literal array is checked against the actual signed spline pullback using the
proved sparse normalization. All Bernstein signs and all geometric vertex inequalities
are evaluated by the ordinary Lean kernel. No external data checker is a proof premise.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

/-- The actual closed rational triangle of majorization leaf 159. -/
def majorizationTriangle159 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 159. -/
def majorizationArray159 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2625815892429876297760162292526951994256625135981 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-51242951650016723 /
    50000000000000000 : ℚ) else
  if p = (0, 3) then (110053300590626099 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (-1596074158722297511885156891945484336684696401823 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 2) then (4464122669540191 /
    6250000000000000 : ℚ) else
  if p = (1, 3) then (-15889252515864949 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-1948217983248093 /
    5000000000000000 : ℚ) else
  if p = (2, 2) then (-913562348890179 /
    10000000000000000 : ℚ) else
  if p = (2, 3) then (-3450105573169711 /
    20000000000000000 : ℚ) else
  if p = (3, 0) then (24673656572515357 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-2023763238858277 /
    50000000000000000 : ℚ) else
  if p = (3, 3) then (82349091781899613 /
    900000000000000000 : ℚ) else
  if p = (0, 1) then (-903103634726627387684911498698446573563342421301 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf159_polynomial_eq :
    lowerPullbackPolynomial 3 0 majorizationTriangle159 radialPowerData3.radius
      (certifiedRadialHeight radialPowerData3 radialPowerData32)
      (certifiedRadialSlope radialPowerData3) 1 =
        planeArrayPolynomial majorizationArray159 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 3 0 majorizationTriangle159
    cellMatrix_3_0 cellMatrix_3_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf159_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray159 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf159_kernel {p : ℝ × ℝ} (hp : majorizationTriangle159.Contains p) :
    (1 : ℝ) ≤ kernel (((3 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 3 0 majorizationTriangle159
    radialPowerData3 radialPowerData32 radialPowerData3_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray159
    majorizationLeaf159_polynomial_eq majorizationLeaf159_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 160. -/
def majorizationTriangle160 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 160. -/
def majorizationArray160 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (271348247224497061378674622319739930534851031109 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (31037605897743989130829190983212314799198540857 /
    14855280471424563298789490688000000000000000000 : ℚ) else
  if p = (0, 2) then (29189456003925019 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-161918727665951221 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (4318684634319779408072359196411489801977584659 /
    4951760157141521099596496896000000000000000000 : ℚ) else
  if p = (1, 1) then (29091692158458013 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (11920444143231801 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-10586516088984323 /
    60000000000000000 : ℚ) else
  if p = (2, 0) then (-76109209859139917 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (2989724414937239 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (291228289446953 /
    3125000000000000 : ℚ) else
  if p = (2, 3) then (-7649377046088487 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (-59971161599998349 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (58063932915600289 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-70206512348749951 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (82349091781899613 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf160_polynomial_eq :
    lowerPullbackPolynomial 3 0 majorizationTriangle160 radialPowerData4.radius
      (certifiedRadialHeight radialPowerData4 radialPowerData32)
      (certifiedRadialSlope radialPowerData4) 1 =
        planeArrayPolynomial majorizationArray160 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 3 0 majorizationTriangle160
    cellMatrix_3_0 cellMatrix_3_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf160_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray160 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf160_kernel {p : ℝ × ℝ} (hp : majorizationTriangle160.Contains p) :
    (1 : ℝ) ≤ kernel (((3 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 3 0 majorizationTriangle160
    radialPowerData4 radialPowerData32 radialPowerData4_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray160
    majorizationLeaf160_polynomial_eq majorizationLeaf160_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 161. -/
def majorizationTriangle161 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 161. -/
def majorizationArray161 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (509907529235362613205444924125576894359471288891 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 1) then (-13336990948732255133920640276075142233890872339 /
    4951760157141521099596496896000000000000000000 : ℚ) else
  if p = (0, 2) then (7567397290592653 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (19014556237527203 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (520693328248243034488217654349076604143692743 /
    14855280471424563298789490688000000000000000000 : ℚ) else
  if p = (1, 1) then (55536710196778107 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (19823728840456579 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (-160705479888464737 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-13070102203942441 /
    20000000000000000 : ℚ) else
  if p = (2, 1) then (-14004566115069849 /
    20000000000000000 : ℚ) else
  if p = (2, 2) then (-12177441417289491 /
    20000000000000000 : ℚ) else
  if p = (2, 3) then (211461579760481691 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (59971161599998349 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (58063932915600289 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (70206512348749951 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-177111664854215867 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf161_polynomial_eq :
    lowerPullbackPolynomial 3 1 majorizationTriangle161 radialPowerData4.radius
      (certifiedRadialHeight radialPowerData4 radialPowerData32)
      (certifiedRadialSlope radialPowerData4) 1 =
        planeArrayPolynomial majorizationArray161 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 3 1 majorizationTriangle161
    cellMatrix_3_1 cellMatrix_3_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf161_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray161 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf161_kernel {p : ℝ × ℝ} (hp : majorizationTriangle161.Contains p) :
    (1 : ℝ) ≤ kernel (((3 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 3 1 majorizationTriangle161
    radialPowerData4 radialPowerData32 radialPowerData4_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray161
    majorizationLeaf161_polynomial_eq majorizationLeaf161_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 162. -/
def majorizationTriangle162 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 162. -/
def majorizationArray162 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (9910347504924478365324550331515558347113256239 /
    4753689750855860255612637020160000000000000000 : ℚ) else
  if p = (0, 1) then (55241613649235230062165006310459765610668058011 /
    38029518006846882044901096161280000000000000000 : ℚ) else
  if p = (0, 2) then (-7377280807705339 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (16102150886193211 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (-1183947660495819645231416253226947562557867001 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (1, 1) then (88707987224621289 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-10873098238833773 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (78206379480632467 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-80705964746125663 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (60702494405706323 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-55423309610813403 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (14812384027083679 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (-4181398035683769 /
    25000000000000000 : ℚ) else
  if p = (3, 1) then (-155746372095331543 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (94672272453227261 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-177111664854215867 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf162_polynomial_eq :
    lowerPullbackPolynomial 3 1 majorizationTriangle162 radialPowerData5.radius
      (certifiedRadialHeight radialPowerData5 radialPowerData32)
      (certifiedRadialSlope radialPowerData5) 1 =
        planeArrayPolynomial majorizationArray162 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 3 1 majorizationTriangle162
    cellMatrix_3_1 cellMatrix_3_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf162_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray162 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf162_kernel {p : ℝ × ℝ} (hp : majorizationTriangle162.Contains p) :
    (1 : ℝ) ≤ kernel (((3 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 3 1 majorizationTriangle162
    radialPowerData5 radialPowerData32 radialPowerData5_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray162
    majorizationLeaf162_polynomial_eq majorizationLeaf162_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 163. -/
def majorizationTriangle163 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 163. -/
def majorizationArray163 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (286696418668798911236033048428293243363747056479 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 1) then (-21302819483364885739082015569949389633774668937 /
    12676506002282294014967032053760000000000000000 : ℚ) else
  if p = (0, 2) then (14435692658753383 /
    40000000000000000 : ℚ) else
  if p = (0, 3) then (23537477939432699 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (10002173030969225681358259824033907040807558881 /
    7605903601369376408980219232256000000000000000 : ℚ) else
  if p = (1, 1) then (-101379768154629151 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-80564304860713579 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (57201924522380189 /
    60000000000000000 : ℚ) else
  if p = (2, 0) then (-181059517602536119 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (250790249784956763 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (512610325108550163 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-184468863180303849 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (4181398035683769 /
    25000000000000000 : ℚ) else
  if p = (3, 1) then (-155746372095331543 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-94672272453227261 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (347084775339123209 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf163_polynomial_eq :
    lowerPullbackPolynomial 3 2 majorizationTriangle163 radialPowerData5.radius
      (certifiedRadialHeight radialPowerData5 radialPowerData32)
      (certifiedRadialSlope radialPowerData5) 1 =
        planeArrayPolynomial majorizationArray163 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 3 2 majorizationTriangle163
    cellMatrix_3_2 cellMatrix_3_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf163_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray163 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf163_kernel {p : ℝ × ℝ} (hp : majorizationTriangle163.Contains p) :
    (1 : ℝ) ≤ kernel (((3 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 3 2 majorizationTriangle163
    radialPowerData5 radialPowerData32 radialPowerData5_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray163
    majorizationLeaf163_polynomial_eq majorizationLeaf163_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 164. -/
def majorizationTriangle164 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 164. -/
def majorizationArray164 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (63629961343316841930337276258418114719568893969 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (133804212338369266258149314919243193817260640349 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (185500060269101789 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-103815951346108903 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-302037637795343534527163123884169338450501117673 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-55829041970392443 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (198902520389182597 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-126634005791675731 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-12358775360530657 /
    24000000000000000 : ℚ) else
  if p = (2, 1) then (-109976808647336613 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (226102612663856339 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-140762961137334871 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (118647422100544469 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (-9870152045482897 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (-82030546663712927 /
    60000000000000000 : ℚ) else
  if p = (3, 3) then (347084775339123209 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf164_polynomial_eq :
    lowerPullbackPolynomial 3 2 majorizationTriangle164 radialPowerData6.radius
      (certifiedRadialHeight radialPowerData6 radialPowerData32)
      (certifiedRadialSlope radialPowerData6) 1 =
        planeArrayPolynomial majorizationArray164 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 3 2 majorizationTriangle164
    cellMatrix_3_2 cellMatrix_3_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf164_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray164 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf164_kernel {p : ℝ × ℝ} (hp : majorizationTriangle164.Contains p) :
    (1 : ℝ) ≤ kernel (((3 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 3 2 majorizationTriangle164
    radialPowerData6 radialPowerData32 radialPowerData6_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray164
    majorizationLeaf164_polynomial_eq majorizationLeaf164_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 165. -/
def majorizationTriangle165 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 165. -/
def majorizationArray165 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (128043798543562041904574859402073265938475263027 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 1) then (13200596653203821028469513140934792140529055651 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (213403330930363109 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-118647422100544469 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (13200596653203821028469513140934792140529055651 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (-335003571537963051 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (33839544184046799 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-9870152045482897 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (213403330930363109 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (33839544184046799 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (-594202853973272931 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (82030546663712927 /
    60000000000000000 : ℚ) else
  if p = (3, 0) then (-118647422100544469 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (-9870152045482897 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (82030546663712927 /
    60000000000000000 : ℚ) else
  if p = (3, 3) then (-1782682143299291 /
    2500000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf165_polynomial_eq :
    lowerPullbackPolynomial 3 3 majorizationTriangle165 radialPowerData6.radius
      (certifiedRadialHeight radialPowerData6 radialPowerData32)
      (certifiedRadialSlope radialPowerData6) 1 =
        planeArrayPolynomial majorizationArray165 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 3 3 majorizationTriangle165
    cellMatrix_3_3 cellMatrix_3_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf165_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray165 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf165_kernel {p : ℝ × ℝ} (hp : majorizationTriangle165.Contains p) :
    (1 : ℝ) ≤ kernel (((3 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 3 3 majorizationTriangle165
    radialPowerData6 radialPowerData32 radialPowerData6_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray165
    majorizationLeaf165_polynomial_eq majorizationLeaf165_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 166. -/
def majorizationTriangle166 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 166. -/
def majorizationArray166 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (35552934553291073280772880075827489708762600709 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (-2770258563909263483627040303262532411737227409 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 2) then (236043203381952181 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-6317892889106299 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (-2770258563909263483627040303262532411737227409 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (1, 1) then (-155775204922885999 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-98956357436689041 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (148929438912935819 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (236043203381952181 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-98956357436689041 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-237123063874503911 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (1852902706153441 /
    2400000000000000 : ℚ) else
  if p = (3, 0) then (-6317892889106299 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (148929438912935819 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (1852902706153441 /
    2400000000000000 : ℚ) else
  if p = (3, 3) then (-1782682143299291 /
    2500000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf166_polynomial_eq :
    lowerPullbackPolynomial 3 3 majorizationTriangle166 radialPowerData7.radius
      (certifiedRadialHeight radialPowerData7 radialPowerData32)
      (certifiedRadialSlope radialPowerData7) 1 =
        planeArrayPolynomial majorizationArray166 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 3 3 majorizationTriangle166
    cellMatrix_3_3 cellMatrix_3_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf166_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray166 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf166_kernel {p : ℝ × ℝ} (hp : majorizationTriangle166.Contains p) :
    (1 : ℝ) ≤ kernel (((3 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 3 3 majorizationTriangle166
    radialPowerData7 radialPowerData32 radialPowerData7_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray166
    majorizationLeaf166_polynomial_eq majorizationLeaf166_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 208. -/
def majorizationTriangle208 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 208. -/
def majorizationArray208 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (690730188593321896085545851000756163917988393531 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (-22121545277004367 /
    50000000000000000 : ℚ) else
  if p = (0, 3) then (161918727665951221 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-16427427349279776653800409121771434520999203897 /
    14855280471424563298789490688000000000000000000 : ℚ) else
  if p = (1, 2) then (20506068150844907 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (-10586516088984323 /
    60000000000000000 : ℚ) else
  if p = (2, 0) then (-14290703092446503 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-5319550730512863 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (7649377046088487 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (7069352177661313 /
    450000000000000000 : ℚ) else
  if p = (3, 2) then (15557467803451223 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-24204094702683523 /
    900000000000000000 : ℚ) else
  if p = (0, 1) then (-8636854186402785574216667669991339366688087059 /
    4951760157141521099596496896000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf208_polynomial_eq :
    lowerPullbackPolynomial 4 0 majorizationTriangle208 radialPowerData4.radius
      (certifiedRadialHeight radialPowerData4 radialPowerData32)
      (certifiedRadialSlope radialPowerData4) 1 =
        planeArrayPolynomial majorizationArray208 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 4 0 majorizationTriangle208
    cellMatrix_4_0 cellMatrix_4_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf208_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray208 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf208_kernel {p : ℝ × ℝ} (hp : majorizationTriangle208.Contains p) :
    (1 : ℝ) ≤ kernel (((4 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 4 0 majorizationTriangle208
    radialPowerData4 radialPowerData32 radialPowerData4_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray208
    majorizationLeaf208_polynomial_eq majorizationLeaf208_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 209. -/
def majorizationTriangle209 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 209. -/
def majorizationArray209 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (216508468662449010163446806818008838892799458753 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (250737361470106147373731805609167724483333913607 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 2) then (3184853115476201 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (-7856601797951633 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (43176264037245172775873866021411973677574454957 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (1, 1) then (755296108948689 /
    6250000000000000 : ℚ) else
  if p = (1, 2) then (1928460517859109 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-2656943129816207 /
    50000000000000000 : ℚ) else
  if p = (2, 0) then (-7900439359229429 /
    60000000000000000 : ℚ) else
  if p = (2, 1) then (5048056755530033 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (168169590767549 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (-85245513088939 /
    4000000000000000 : ℚ) else
  if p = (3, 0) then (-9151753265748193 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (2303613634739641 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (86466268992323 /
    3000000000000000 : ℚ) else
  if p = (3, 3) then (-24204094702683523 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf209_polynomial_eq :
    lowerPullbackPolynomial 4 0 majorizationTriangle209 radialPowerData5.radius
      (certifiedRadialHeight radialPowerData5 radialPowerData32)
      (certifiedRadialSlope radialPowerData5) 1 =
        planeArrayPolynomial majorizationArray209 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 4 0 majorizationTriangle209
    cellMatrix_4_0 cellMatrix_4_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf209_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray209 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf209_kernel {p : ℝ × ℝ} (hp : majorizationTriangle209.Contains p) :
    (1 : ℝ) ≤ kernel (((4 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 4 0 majorizationTriangle209
    radialPowerData5 radialPowerData32 radialPowerData5_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray209
    majorizationLeaf209_polynomial_eq majorizationLeaf209_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 210. -/
def majorizationTriangle210 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 210. -/
def majorizationArray210 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2022339199375411572168543255893643897059929416221 /
    570442770102703230673516442419200000000000000000 : ℚ) else
  if p = (0, 1) then (-287695223125076770200423981553642759670114614279 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 2) then (29189456003925019 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-16102150886193211 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (-3750090506122215906385928674048422575754169481 /
    12676506002282294014967032053760000000000000000 : ℚ) else
  if p = (1, 1) then (29091692158458013 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-11920444143231801 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (78206379480632467 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-76109209859139917 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-2989724414937239 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (291228289446953 /
    3125000000000000 : ℚ) else
  if p = (2, 3) then (-14812384027083679 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (9151753265748193 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (2303613634739641 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (-86466268992323 /
    3000000000000000 : ℚ) else
  if p = (3, 3) then (7965620216763439 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf210_polynomial_eq :
    lowerPullbackPolynomial 4 1 majorizationTriangle210 radialPowerData5.radius
      (certifiedRadialHeight radialPowerData5 radialPowerData32)
      (certifiedRadialSlope radialPowerData5) 1 =
        planeArrayPolynomial majorizationArray210 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 4 1 majorizationTriangle210
    cellMatrix_4_1 cellMatrix_4_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf210_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray210 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf210_kernel {p : ℝ × ℝ} (hp : majorizationTriangle210.Contains p) :
    (1 : ℝ) ≤ kernel (((4 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 4 1 majorizationTriangle210
    radialPowerData5 radialPowerData32 radialPowerData5_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray210
    majorizationLeaf210_polynomial_eq majorizationLeaf210_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 211. -/
def majorizationTriangle211 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 211. -/
def majorizationArray211 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (138610877761540819590546459349540652913389213713 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (423934021202362973177346740598074259620277311767 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (363650380991959 /
    7500000000000000 : ℚ) else
  if p = (0, 3) then (-451650694443389 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (38154493847693126521889892451617415179465148509 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (227859432194853 /
    2500000000000000 : ℚ) else
  if p = (1, 2) then (208379987505159 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (147760096722219 /
    50000000000000000 : ℚ) else
  if p = (2, 0) then (-26907000532900189 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (4888369121663363 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-256495364601763 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (592834546136861 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (-134489892106776233 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (50925756162379597 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-54397328152406351 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (7965620216763439 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf211_polynomial_eq :
    lowerPullbackPolynomial 4 1 majorizationTriangle211 radialPowerData6.radius
      (certifiedRadialHeight radialPowerData6 radialPowerData32)
      (certifiedRadialSlope radialPowerData6) 1 =
        planeArrayPolynomial majorizationArray211 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 4 1 majorizationTriangle211
    cellMatrix_4_1 cellMatrix_4_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf211_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray211 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf211_kernel {p : ℝ × ℝ} (hp : majorizationTriangle211.Contains p) :
    (1 : ℝ) ≤ kernel (((4 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 4 1 majorizationTriangle211
    radialPowerData6 radialPowerData32 radialPowerData6_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray211
    majorizationLeaf211_polynomial_eq majorizationLeaf211_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
