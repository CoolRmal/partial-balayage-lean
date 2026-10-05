/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices4

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

/-- The actual closed rational triangle of majorization leaf 306. -/
def majorizationTriangle306 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 306. -/
def majorizationArray306 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (210722775615500771891748324803947307843394402563 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 1) then (-19488812626225271650899065874765170289007374153 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (0, 2) then (1719726389573413 /
    40000000000000000 : ℚ) else
  if p = (0, 3) then (-88290755502731 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (-8144405368262637305256443712517714863284227547 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (1, 1) then (-64102914740509 /
    8000000000000000 : ℚ) else
  if p = (1, 2) then (-4392224340846233 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-83542155970259 /
    12500000000000000 : ℚ) else
  if p = (2, 0) then (-19585771398031673 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-1540005744905973 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (1012577781563391 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (602298887756389 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (9931555334817859 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (1750747491053381 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-92593972961449 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-1607224183257691 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf306_polynomial_eq :
    lowerPullbackPolynomial 6 3 majorizationTriangle306 radialPowerData9.radius
      (certifiedRadialHeight radialPowerData9 radialPowerData32)
      (certifiedRadialSlope radialPowerData9) 1 =
        planeArrayPolynomial majorizationArray306 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 3 majorizationTriangle306
    cellMatrix_6_3 cellMatrix_6_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf306_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray306 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf306_kernel {p : ℝ × ℝ} (hp : majorizationTriangle306.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 3 majorizationTriangle306
    radialPowerData9 radialPowerData32 radialPowerData9_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray306
    majorizationLeaf306_polynomial_eq majorizationLeaf306_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 307. -/
def majorizationTriangle307 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 307. -/
def majorizationArray307 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (51607436047509429229559292365261644267166105639 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (2051935090140511321053528511480027039360178379 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (0, 2) then (586675112575093 /
    37500000000000000 : ℚ) else
  if p = (0, 3) then (2996186222833417 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (4311153863182058753959138494277717101207882337 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (-513651466280627 /
    12500000000000000 : ℚ) else
  if p = (1, 2) then (82554246769217 /
    6250000000000000 : ℚ) else
  if p = (1, 3) then (1557399994427 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-12863345201569567 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-4061871936579 /
    390625000000000 : ℚ) else
  if p = (2, 2) then (283535205675499 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-49918120002869 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (-30999114354445297 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-134617647548713 /
    40000000000000000 : ℚ) else
  if p = (3, 2) then (3492230285399729 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-1607224183257691 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf307_polynomial_eq :
    lowerPullbackPolynomial 6 3 majorizationTriangle307 radialPowerData10.radius
      (certifiedRadialHeight radialPowerData10 radialPowerData32)
      (certifiedRadialSlope radialPowerData10) 1 =
        planeArrayPolynomial majorizationArray307 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 3 majorizationTriangle307
    cellMatrix_6_3 cellMatrix_6_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf307_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray307 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf307_kernel {p : ℝ × ℝ} (hp : majorizationTriangle307.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 3 majorizationTriangle307
    radialPowerData10 radialPowerData32 radialPowerData10_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray307
    majorizationLeaf307_polynomial_eq majorizationLeaf307_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 308. -/
def majorizationTriangle308 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 308. -/
def majorizationArray308 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (96114643786481890008820240249237098040459274693 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 1) then (-1508668068530711228924656280732863518749055179 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (0, 2) then (8068887414850679 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-4208585775185869 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-228304059244308471582937064429471474842339937 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (-14397045036777623 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-1680449565483733 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (11142497681424307 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-18908601585861477 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (4098943144759143 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (185054844324069 /
    8000000000000000 : ℚ) else
  if p = (2, 3) then (-1900497464413367 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (30999114354445297 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-134617647548713 /
    40000000000000000 : ℚ) else
  if p = (3, 2) then (-3492230285399729 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (341170778056439 /
    150000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf308_polynomial_eq :
    lowerPullbackPolynomial 6 4 majorizationTriangle308 radialPowerData10.radius
      (certifiedRadialHeight radialPowerData10 radialPowerData32)
      (certifiedRadialSlope radialPowerData10) 1 =
        planeArrayPolynomial majorizationArray308 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 4 majorizationTriangle308
    cellMatrix_6_4 cellMatrix_6_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf308_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray308 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf308_kernel {p : ℝ × ℝ} (hp : majorizationTriangle308.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 4 majorizationTriangle308
    radialPowerData10 radialPowerData32 radialPowerData10_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray308
    majorizationLeaf308_polynomial_eq majorizationLeaf308_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 309. -/
def majorizationTriangle309 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 309. -/
def majorizationArray309 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (4907235178430389942744725039169602931872656029 /
    8913168282854737979273694412800000000000000000 : ℚ) else
  if p = (0, 1) then (143922110580253235104647518534313351743000743889 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-8073404974241447 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (388004595009843 /
    40000000000000000 : ℚ) else
  if p = (1, 0) then (44175244097418208691013619643750739117957339803 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-9668333022098547 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-1191826335006429 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (3833562231621373 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-3538535139402127 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (-2740517020369607 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-473302233860837 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (535814352187611 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-18558678695231293 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-981935189470577 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (-601819051277539 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (341170778056439 /
    150000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf309_polynomial_eq :
    lowerPullbackPolynomial 6 4 majorizationTriangle309 radialPowerData11.radius
      (certifiedRadialHeight radialPowerData11 radialPowerData32)
      (certifiedRadialSlope radialPowerData11) 1 =
        planeArrayPolynomial majorizationArray309 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 4 majorizationTriangle309
    cellMatrix_6_4 cellMatrix_6_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf309_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray309 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf309_kernel {p : ℝ × ℝ} (hp : majorizationTriangle309.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 4 majorizationTriangle309
    radialPowerData11 radialPowerData32 radialPowerData11_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray309
    majorizationLeaf309_polynomial_eq majorizationLeaf309_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 310. -/
def majorizationTriangle310 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 310. -/
def majorizationArray310 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (618126520871358879470222752653302040588711765649 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 1) then (-25718198412160027769328402394796570640872790683 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-284804369419183 /
    12500000000000000 : ℚ) else
  if p = (0, 3) then (-4083234730714807 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-47048004640541277647943281871957339341217796049 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-10029521505095323 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (1370124927002821 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (510665141698029 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-1510473099676747 /
    25000000000000000 : ℚ) else
  if p = (2, 1) then (1912548241930623 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-134390160642297 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (-1227705118346011 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (18558678695231293 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-981935189470577 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (601819051277539 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (148968037024171 /
    225000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf310_polynomial_eq :
    lowerPullbackPolynomial 6 5 majorizationTriangle310 radialPowerData11.radius
      (certifiedRadialHeight radialPowerData11 radialPowerData32)
      (certifiedRadialSlope radialPowerData11) 1 =
        planeArrayPolynomial majorizationArray310 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 5 majorizationTriangle310
    cellMatrix_6_5 cellMatrix_6_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf310_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray310 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf310_kernel {p : ℝ × ℝ} (hp : majorizationTriangle310.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 5 majorizationTriangle310
    radialPowerData11 radialPowerData32 radialPowerData11_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray310
    majorizationLeaf310_polynomial_eq majorizationLeaf310_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 311. -/
def majorizationTriangle311 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 311. -/
def majorizationArray311 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (7237864551138579856538773446482734098013484479 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (66812760602717728659767097140275137887979587077 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-5026012244259329 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (1978619514277211 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (22229625236057007694444906965968086398273722199 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (-438521929218141 /
    12500000000000000 : ℚ) else
  if p = (1, 2) then (-730077909800931 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (89443161531811 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-1365874019954621 /
    75000000000000000 : ℚ) else
  if p = (2, 1) then (-175795173049529 /
    20000000000000000 : ℚ) else
  if p = (2, 2) then (-12731576400337 /
    5000000000000000 : ℚ) else
  if p = (2, 3) then (35960822152643 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-758539144799847 /
    200000000000000000 : ℚ) else
  if p = (3, 1) then (-838097849534813 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-597854449156969 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (148968037024171 /
    225000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf311_polynomial_eq :
    lowerPullbackPolynomial 6 5 majorizationTriangle311 radialPowerData12.radius
      (certifiedRadialHeight radialPowerData12 radialPowerData32)
      (certifiedRadialSlope radialPowerData12) 1 =
        planeArrayPolynomial majorizationArray311 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 5 majorizationTriangle311
    cellMatrix_6_5 cellMatrix_6_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf311_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray311 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf311_kernel {p : ℝ × ℝ} (hp : majorizationTriangle311.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 5 majorizationTriangle311
    radialPowerData12 radialPowerData32 radialPowerData12_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray311
    majorizationLeaf311_polynomial_eq majorizationLeaf311_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 312. -/
def majorizationTriangle312 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 312. -/
def majorizationArray312 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (747715236259738156382611693176293430835537747391 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-43965575858467821160424071671182603788632868357 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-17753844462835591 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (758539144799847 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-43965575858467821160424071671182603788632868357 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-521861915083411 /
    8000000000000000 : ℚ) else
  if p = (1, 2) then (4272245279099729 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-838097849534813 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-17753844462835591 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (4272245279099729 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-2302826403484387 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (597854449156969 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (758539144799847 /
    200000000000000000 : ℚ) else
  if p = (3, 1) then (-838097849534813 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (597854449156969 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-905737875261053 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf312_polynomial_eq :
    lowerPullbackPolynomial 6 6 majorizationTriangle312 radialPowerData12.radius
      (certifiedRadialHeight radialPowerData12 radialPowerData32)
      (certifiedRadialSlope radialPowerData12) 1 =
        planeArrayPolynomial majorizationArray312 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 6 majorizationTriangle312
    cellMatrix_6_6 cellMatrix_6_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf312_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray312 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf312_kernel {p : ℝ × ℝ} (hp : majorizationTriangle312.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 6 majorizationTriangle312
    radialPowerData12 radialPowerData32 radialPowerData12_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray312
    majorizationLeaf312_polynomial_eq majorizationLeaf312_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 313. -/
def majorizationTriangle313 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 313. -/
def majorizationArray313 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (19036297546874225455220881407989433098874786197 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (4077374479213704223467209661770936102635210951 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (0, 2) then (-7198838539242737 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-2853185949275921 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (4077374479213704223467209661770936102635210951 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (-4834681832471263 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-721513215417131 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-738642604184731 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-7198838539242737 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-721513215417131 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-527175459064679 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (17912403051199 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-2853185949275921 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-738642604184731 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (17912403051199 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-905737875261053 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf313_polynomial_eq :
    lowerPullbackPolynomial 6 6 majorizationTriangle313 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray313 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 6 majorizationTriangle313
    cellMatrix_6_6 cellMatrix_6_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf313_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray313 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf313_kernel {p : ℝ × ℝ} (hp : majorizationTriangle313.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 6 majorizationTriangle313
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray313
    majorizationLeaf313_polynomial_eq majorizationLeaf313_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 343. -/
def majorizationTriangle343 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 343. -/
def majorizationArray343 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (299696538455034522432181141776092782197195107 /
    116056878683004400771792896000000000000000000 : ℚ) else
  if p = (0, 2) then (-1055766498123203 /
    20000000000000000 : ℚ) else
  if p = (0, 3) then (21674719072611743 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-18324777011591923662900192044514644329337470831 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (1, 2) then (633362578154823 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (-644333910738379 /
    50000000000000000 : ℚ) else
  if p = (2, 0) then (-1677677702605161 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-1017471514787781 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (299817167788907 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (3705232517993179 /
    900000000000000000 : ℚ) else
  if p = (3, 2) then (265680507764237 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (-1244770389182459 /
    1800000000000000000 : ℚ) else
  if p = (0, 1) then (-24568668060188831557018061107478823441287888751 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf343_polynomial_eq :
    lowerPullbackPolynomial 7 0 majorizationTriangle343 radialPowerData7.radius
      (certifiedRadialHeight radialPowerData7 radialPowerData32)
      (certifiedRadialSlope radialPowerData7) 1 =
        planeArrayPolynomial majorizationArray343 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 0 majorizationTriangle343
    cellMatrix_7_0 cellMatrix_7_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf343_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray343 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf343_kernel {p : ℝ × ℝ} (hp : majorizationTriangle343.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 0 majorizationTriangle343
    radialPowerData7 radialPowerData32 radialPowerData7_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray343
    majorizationLeaf343_polynomial_eq majorizationLeaf343_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 344. -/
def majorizationTriangle344 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 344. -/
def majorizationArray344 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2182388059284096363997013730033760772749816981 /
    1426106925256758076683791106048000000000000000 : ℚ) else
  if p = (0, 1) then (39151905750231964916340154391823921830616568417 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (0, 2) then (8390034339672013 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-26104258996393151 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (87015918601196623050285856736555871418227177251 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (2473220873487613 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (853240879966441 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-278646842228033 /
    40000000000000000 : ℚ) else
  if p = (2, 0) then (-14484563437702619 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (790675043908431 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (181545954610183 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-1153766953128797 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-3117953579991581 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (880673672931437 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (60682786041837 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-1244770389182459 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf344_polynomial_eq :
    lowerPullbackPolynomial 7 0 majorizationTriangle344 radialPowerData8.radius
      (certifiedRadialHeight radialPowerData8 radialPowerData32)
      (certifiedRadialSlope radialPowerData8) 1 =
        planeArrayPolynomial majorizationArray344 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 0 majorizationTriangle344
    cellMatrix_7_0 cellMatrix_7_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf344_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray344 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf344_kernel {p : ℝ × ℝ} (hp : majorizationTriangle344.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 0 majorizationTriangle344
    radialPowerData8 radialPowerData32 radialPowerData8_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray344
    majorizationLeaf344_polynomial_eq majorizationLeaf344_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 345. -/
def majorizationTriangle345 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 345. -/
def majorizationArray345 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1331322559261568355677204547452283784459061254253 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 1) then (-121683475177697589553771382461420588718838331171 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (2919110800381849 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (2592749961901283 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-23944873049026433238672124928938897952021353057 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (1, 1) then (616905579279489 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (-699190573656159 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-6847249086443 /
    8000000000000000 : ℚ) else
  if p = (2, 0) then (-11919212088838681 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-417837179209967 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (181797156367847 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (1130233242023 /
    24000000000000000 : ℚ) else
  if p = (3, 0) then (3117953579991581 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (880673672931437 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-60682786041837 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (3316570853923 /
    120000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf345_polynomial_eq :
    lowerPullbackPolynomial 7 1 majorizationTriangle345 radialPowerData8.radius
      (certifiedRadialHeight radialPowerData8 radialPowerData32)
      (certifiedRadialSlope radialPowerData8) 1 =
        planeArrayPolynomial majorizationArray345 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 1 majorizationTriangle345
    cellMatrix_7_1 cellMatrix_7_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf345_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray345 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf345_kernel {p : ℝ × ℝ} (hp : majorizationTriangle345.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 1 majorizationTriangle345
    radialPowerData8 radialPowerData32 radialPowerData8_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray345
    majorizationLeaf345_polynomial_eq majorizationLeaf345_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 346. -/
def majorizationTriangle346 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 346. -/
def majorizationArray346 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (8739487273791082505964621162825879355971261559 /
    7922816251426433759354395033600000000000000000 : ℚ) else
  if p = (0, 1) then (69441733655590167255929208954954135568438463963 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 2) then (3192223104361397 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-593317486706089 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (3291511148304261594800223017935019335399082357 /
    12676506002282294014967032053760000000000000000 : ℚ) else
  if p = (1, 1) then (359455656981501 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (1260524336539671 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-40728345657323 /
    60000000000000000 : ℚ) else
  if p = (2, 0) then (-5411315437245981 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (69915748165729 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (259550348469603 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-3900219692971 /
    30000000000000000 : ℚ) else
  if p = (3, 0) then (-638860291511187 /
    100000000000000000 : ℚ) else
  if p = (3, 1) then (28316275974463 /
    30000000000000000 : ℚ) else
  if p = (3, 2) then (22049965886111 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (3316570853923 /
    120000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf346_polynomial_eq :
    lowerPullbackPolynomial 7 1 majorizationTriangle346 radialPowerData9.radius
      (certifiedRadialHeight radialPowerData9 radialPowerData32)
      (certifiedRadialSlope radialPowerData9) 1 =
        planeArrayPolynomial majorizationArray346 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 1 majorizationTriangle346
    cellMatrix_7_1 cellMatrix_7_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf346_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray346 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf346_kernel {p : ℝ × ℝ} (hp : majorizationTriangle346.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 1 majorizationTriangle346
    radialPowerData9 radialPowerData32 radialPowerData9_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray346
    majorizationLeaf346_polynomial_eq majorizationLeaf346_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
