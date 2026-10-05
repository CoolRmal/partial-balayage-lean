/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices3

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

/-- The actual closed rational triangle of majorization leaf 261. -/
def majorizationTriangle261 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 261. -/
def majorizationArray261 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (90733906054760472756341224671025318003256206917 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (0, 1) then (-106672300485369349200172307187566507024394565411 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (8231759076908331 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (32179971487811243 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (51085128135282038332383811583451714914250836189 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (27042599776668709 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (10897645076132059 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-28831769254266563 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-51770875658978907 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-27105166900275461 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-16302447198541683 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (26290496983229641 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (16092552130473617 /
    300000000000000000 : ℚ) else
  if p = (3, 1) then (1597822572210593 /
    37500000000000000 : ℚ) else
  if p = (3, 2) then (2885837496684179 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-25085899207716863 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf261_polynomial_eq :
    lowerPullbackPolynomial 5 3 majorizationTriangle261 radialPowerData8.radius
      (certifiedRadialHeight radialPowerData8 radialPowerData32)
      (certifiedRadialSlope radialPowerData8) 1 =
        planeArrayPolynomial majorizationArray261 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 5 3 majorizationTriangle261
    cellMatrix_5_3 cellMatrix_5_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf261_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray261 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf261_kernel {p : ℝ × ℝ} (hp : majorizationTriangle261.Contains p) :
    (1 : ℝ) ≤ kernel (((5 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 5 3 majorizationTriangle261
    radialPowerData8 radialPowerData32 radialPowerData8_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray261
    majorizationLeaf261_polynomial_eq majorizationLeaf261_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 262. -/
def majorizationTriangle262 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 262. -/
def majorizationArray262 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (801317503527024907284599778724823868566102317 /
    950737950171172051122527404032000000000000000 : ℚ) else
  if p = (0, 1) then (14206664895109075705690520190185222230119526217 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (0, 2) then (8068887414850679 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (88290755502731 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (15114713748701145739848957192833304569367694811 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (1, 1) then (-14397045036777623 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (1680449565483733 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-83542155970259 /
    12500000000000000 : ℚ) else
  if p = (2, 0) then (-18908601585861477 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-4098943144759143 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (185054844324069 /
    8000000000000000 : ℚ) else
  if p = (2, 3) then (-602298887756389 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-49979391188704933 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-15062486507570953 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (3862844842869701 /
    40000000000000000 : ℚ) else
  if p = (3, 3) then (-25085899207716863 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf262_polynomial_eq :
    lowerPullbackPolynomial 5 3 majorizationTriangle262 radialPowerData9.radius
      (certifiedRadialHeight radialPowerData9 radialPowerData32)
      (certifiedRadialSlope radialPowerData9) 1 =
        planeArrayPolynomial majorizationArray262 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 5 3 majorizationTriangle262
    cellMatrix_5_3 cellMatrix_5_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf262_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray262 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf262_kernel {p : ℝ × ℝ} (hp : majorizationTriangle262.Contains p) :
    (1 : ℝ) ≤ kernel (((5 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 5 3 majorizationTriangle262
    radialPowerData9 radialPowerData32 radialPowerData9_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray262
    majorizationLeaf262_polynomial_eq majorizationLeaf262_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 263. -/
def majorizationTriangle263 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 263. -/
def majorizationArray263 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (9437465868793999428857453152933421008305603533 /
    12676506002282294014967032053760000000000000000 : ℚ) else
  if p = (0, 1) then (-20261664279659756777605965111180249138301177307 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 2) then (20205865282359787 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (-184234344690739843 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (68356840405541947807609656252386692773481345573 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (1, 1) then (-18828708916933431 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-7559766268666763 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (118370584957978307 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-6888799277456641 /
    20000000000000000 : ℚ) else
  if p = (2, 1) then (1197589353270631 /
    12500000000000000 : ℚ) else
  if p = (2, 2) then (1564226093778681 /
    5000000000000000 : ℚ) else
  if p = (2, 3) then (-101526594883313899 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (49979391188704933 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-15062486507570953 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-3862844842869701 /
    40000000000000000 : ℚ) else
  if p = (3, 3) then (47912551245036899 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf263_polynomial_eq :
    lowerPullbackPolynomial 5 4 majorizationTriangle263 radialPowerData9.radius
      (certifiedRadialHeight radialPowerData9 radialPowerData32)
      (certifiedRadialSlope radialPowerData9) 1 =
        planeArrayPolynomial majorizationArray263 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 5 4 majorizationTriangle263
    cellMatrix_5_4 cellMatrix_5_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf263_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray263 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf263_kernel {p : ℝ × ℝ} (hp : majorizationTriangle263.Contains p) :
    (1 : ℝ) ≤ kernel (((5 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 5 4 majorizationTriangle263
    radialPowerData9 radialPowerData32 radialPowerData9_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray263
    majorizationLeaf263_polynomial_eq majorizationLeaf263_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 264. -/
def majorizationTriangle264 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 264. -/
def majorizationArray264 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (16060892301314838039363945628452786194584436749 /
    23768448754279301278063185100800000000000000000 : ℚ) else
  if p = (0, 1) then (1334761385048684897111481528378645882656086219 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (0, 2) then (-284804369419183 /
    12500000000000000 : ℚ) else
  if p = (0, 3) then (4208585775185869 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (3063453199022967014458134419122426004799490657 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (-10029521505095323 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-1370124927002821 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (11142497681424307 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1510473099676747 /
    25000000000000000 : ℚ) else
  if p = (2, 1) then (-1912548241930623 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-134390160642297 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (1900497464413367 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-26747798604339193 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-2341515286905879 /
    40000000000000000 : ℚ) else
  if p = (3, 2) then (-37882429847028283 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (47912551245036899 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf264_polynomial_eq :
    lowerPullbackPolynomial 5 4 majorizationTriangle264 radialPowerData10.radius
      (certifiedRadialHeight radialPowerData10 radialPowerData32)
      (certifiedRadialSlope radialPowerData10) 1 =
        planeArrayPolynomial majorizationArray264 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 5 4 majorizationTriangle264
    cellMatrix_5_4 cellMatrix_5_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf264_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray264 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf264_kernel {p : ℝ × ℝ} (hp : majorizationTriangle264.Contains p) :
    (1 : ℝ) ≤ kernel (((5 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 5 4 majorizationTriangle264
    radialPowerData10 radialPowerData32 radialPowerData10_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray264
    majorizationLeaf264_polynomial_eq majorizationLeaf264_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 265. -/
def majorizationTriangle265 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 265. -/
def majorizationArray265 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (250835914092559175459422787780657864442167983439 /
    356526731314189519170947776512000000000000000000 : ℚ) else
  if p = (0, 1) then (617064627205858068856072429608754214472689461 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (0, 2) then (-62999152996581121 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (26747798604339193 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (617064627205858068856072429608754214472689461 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (1, 1) then (-14096431649844763 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (42772922271310677 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-2341515286905879 /
    40000000000000000 : ℚ) else
  if p = (2, 0) then (-62999152996581121 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (42772922271310677 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-38957551132166659 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (37882429847028283 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (26747798604339193 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-2341515286905879 /
    40000000000000000 : ℚ) else
  if p = (3, 2) then (37882429847028283 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-19555067482687147 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf265_polynomial_eq :
    lowerPullbackPolynomial 5 5 majorizationTriangle265 radialPowerData10.radius
      (certifiedRadialHeight radialPowerData10 radialPowerData32)
      (certifiedRadialSlope radialPowerData10) 1 =
        planeArrayPolynomial majorizationArray265 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 5 5 majorizationTriangle265
    cellMatrix_5_5 cellMatrix_5_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf265_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray265 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf265_kernel {p : ℝ × ℝ} (hp : majorizationTriangle265.Contains p) :
    (1 : ℝ) ≤ kernel (((5 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 5 5 majorizationTriangle265
    radialPowerData10 radialPowerData32 radialPowerData10_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray265
    majorizationLeaf265_polynomial_eq majorizationLeaf265_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 266. -/
def majorizationTriangle266 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 266. -/
def majorizationArray266 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (4848311861989138181586688744714152244548627101 /
    8913168282854737979273694412800000000000000000 : ℚ) else
  if p = (0, 1) then (126948630514081270952798279450899082016350212049 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-17753844462835591 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (4083234730714807 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (126948630514081270952798279450899082016350212049 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-521861915083411 /
    8000000000000000 : ℚ) else
  if p = (1, 2) then (-4272245279099729 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (510665141698029 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-17753844462835591 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-4272245279099729 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-2302826403484387 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (1227705118346011 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (4083234730714807 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (510665141698029 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (1227705118346011 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-19555067482687147 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf266_polynomial_eq :
    lowerPullbackPolynomial 5 5 majorizationTriangle266 radialPowerData11.radius
      (certifiedRadialHeight radialPowerData11 radialPowerData32)
      (certifiedRadialSlope radialPowerData11) 1 =
        planeArrayPolynomial majorizationArray266 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 5 5 majorizationTriangle266
    cellMatrix_5_5 cellMatrix_5_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf266_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray266 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf266_kernel {p : ℝ × ℝ} (hp : majorizationTriangle266.Contains p) :
    (1 : ℝ) ≤ kernel (((5 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 5 5 majorizationTriangle266
    radialPowerData11 radialPowerData32 radialPowerData11_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray266
    majorizationLeaf266_polynomial_eq majorizationLeaf266_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 300. -/
def majorizationTriangle300 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 300. -/
def majorizationArray300 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (4725967866586108687979823801486770941802107399321 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 2) then (-7356492135545989 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (75825506778068557 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-277826787466879697151128370840246017137083210007 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 2) then (62383737739999 /
    1000000000000000 : ℚ) else
  if p = (1, 3) then (-14613517432812719 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-845500356511493 /
    15000000000000000 : ℚ) else
  if p = (2, 2) then (-513522342109501 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (896594632328183 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (3421970457299447 /
    450000000000000000 : ℚ) else
  if p = (3, 2) then (1036617853650223 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-694811939776553 /
    600000000000000000 : ℚ) else
  if p = (0, 1) then (-131832924836964704239286176634727211883575658589 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf300_polynomial_eq :
    lowerPullbackPolynomial 6 0 majorizationTriangle300 radialPowerData6.radius
      (certifiedRadialHeight radialPowerData6 radialPowerData32)
      (certifiedRadialSlope radialPowerData6) 1 =
        planeArrayPolynomial majorizationArray300 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 0 majorizationTriangle300
    cellMatrix_6_0 cellMatrix_6_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf300_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray300 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf300_kernel {p : ℝ × ℝ} (hp : majorizationTriangle300.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 0 majorizationTriangle300
    radialPowerData6 radialPowerData32 radialPowerData6_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray300
    majorizationLeaf300_polynomial_eq majorizationLeaf300_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 301. -/
def majorizationTriangle301 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 301. -/
def majorizationArray301 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (137863109097500282071193605880066138813784790277 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (77666729308450087059558780012963739295038619213 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (2919110800381849 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-21674719072611743 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (17580767097713647380227092058553930621217161071 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (1, 1) then (616905579279489 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (699190573656159 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-644333910738379 /
    50000000000000000 : ℚ) else
  if p = (2, 0) then (-11919212088838681 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (417837179209967 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (181797156367847 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-299817167788907 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (-17823153131769467 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (2062035595271233 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (11200112029213 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-694811939776553 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf301_polynomial_eq :
    lowerPullbackPolynomial 6 0 majorizationTriangle301 radialPowerData7.radius
      (certifiedRadialHeight radialPowerData7 radialPowerData32)
      (certifiedRadialSlope radialPowerData7) 1 =
        planeArrayPolynomial majorizationArray301 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 0 majorizationTriangle301
    cellMatrix_6_0 cellMatrix_6_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf301_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray301 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf301_kernel {p : ℝ × ℝ} (hp : majorizationTriangle301.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 0 majorizationTriangle301
    radialPowerData7 radialPowerData32 radialPowerData7_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray301
    majorizationLeaf301_polynomial_eq majorizationLeaf301_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 302. -/
def majorizationTriangle302 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 302. -/
def majorizationArray302 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (810397608494702815615502734850892739518612521 /
    348170636049013202315378688000000000000000000 : ℚ) else
  if p = (0, 1) then (-27333623141405376876712917495842117803078598511 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 2) then (3394713938740129 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (87877113002617 /
    37500000000000000 : ℚ) else
  if p = (1, 0) then (-13256229795624954717044585599422318982577012591 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (1, 1) then (10339977663186881 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-2136769884812919 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-142502067051827 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-41661577309446829 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-3733384312111101 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (374794424764907 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (2350729639459 /
    50000000000000000 : ℚ) else
  if p = (3, 0) then (17823153131769467 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (2062035595271233 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-11200112029213 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (47075377067 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf302_polynomial_eq :
    lowerPullbackPolynomial 6 1 majorizationTriangle302 radialPowerData7.radius
      (certifiedRadialHeight radialPowerData7 radialPowerData32)
      (certifiedRadialSlope radialPowerData7) 1 =
        planeArrayPolynomial majorizationArray302 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 1 majorizationTriangle302
    cellMatrix_6_1 cellMatrix_6_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf302_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray302 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf302_kernel {p : ℝ × ℝ} (hp : majorizationTriangle302.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 1 majorizationTriangle302
    radialPowerData7 radialPowerData32 radialPowerData7_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray302
    majorizationLeaf302_polynomial_eq majorizationLeaf302_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 303. -/
def majorizationTriangle303 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 303. -/
def majorizationArray303 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5450976527214251484473266927072889899497170789 /
    3961408125713216879677197516800000000000000000 : ℚ) else
  if p = (0, 1) then (111405349705403856895515125231247192965730875171 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (4756397721142893 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-2592749961901283 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (22611588943787226765036165153838178809570071137 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (1, 1) then (1624938658128051 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (1911924828795543 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-6847249086443 /
    8000000000000000 : ℚ) else
  if p = (2, 0) then (-9244477186313103 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (183180852063581 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (391850143786269 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-1130233242023 /
    24000000000000000 : ℚ) else
  if p = (3, 0) then (-11987853328436297 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (1019841223294937 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (5576518326073 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (47075377067 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf303_polynomial_eq :
    lowerPullbackPolynomial 6 1 majorizationTriangle303 radialPowerData8.radius
      (certifiedRadialHeight radialPowerData8 radialPowerData32)
      (certifiedRadialSlope radialPowerData8) 1 =
        planeArrayPolynomial majorizationArray303 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 1 majorizationTriangle303
    cellMatrix_6_1 cellMatrix_6_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf303_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray303 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf303_kernel {p : ℝ × ℝ} (hp : majorizationTriangle303.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 1 majorizationTriangle303
    radialPowerData8 radialPowerData32 radialPowerData8_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray303
    majorizationLeaf303_polynomial_eq majorizationLeaf303_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 304. -/
def majorizationTriangle304 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 304. -/
def majorizationArray304 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1142223287136177088153275829467340524395531556973 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 1) then (-115232945902171239390107597067797175791273981731 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (21191671117826261 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (2302112362887467 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-36364322688037815015240135121136576018291177251 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (1099285925070747 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-2706778153020227 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-280907697971001 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-51709138215811903 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-2955586706907779 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (80600636087683 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (38098412570311 /
    37500000000000000 : ℚ) else
  if p = (3, 0) then (11987853328436297 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (1019841223294937 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-5576518326073 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-266628882232201 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf304_polynomial_eq :
    lowerPullbackPolynomial 6 2 majorizationTriangle304 radialPowerData8.radius
      (certifiedRadialHeight radialPowerData8 radialPowerData32)
      (certifiedRadialSlope radialPowerData8) 1 =
        planeArrayPolynomial majorizationArray304 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 2 majorizationTriangle304
    cellMatrix_6_2 cellMatrix_6_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf304_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray304 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf304_kernel {p : ℝ × ℝ} (hp : majorizationTriangle304.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 2 majorizationTriangle304
    radialPowerData8 radialPowerData32 radialPowerData8_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray304
    majorizationLeaf304_polynomial_eq majorizationLeaf304_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 305. -/
def majorizationTriangle305 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 305. -/
def majorizationArray305 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (23388108702012220536987385747363081788564208997 /
    23768448754279301278063185100800000000000000000 : ℚ) else
  if p = (0, 1) then (60899372600878800730775572308357537707295968731 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 2) then (2563195707811387 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (-369993694479881 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (35943971110197944690926466494356191590869831131 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (1, 1) then (-293183686727129 /
    20000000000000000 : ℚ) else
  if p = (1, 2) then (1322425348301899 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-146585173561651 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-4827108031606907 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (-13171359134213 /
    12500000000000000 : ℚ) else
  if p = (2, 2) then (183698965669761 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-4572609585237 /
    8000000000000000 : ℚ) else
  if p = (3, 0) then (-9931555334817859 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (1750747491053381 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (92593972961449 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-266628882232201 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf305_polynomial_eq :
    lowerPullbackPolynomial 6 2 majorizationTriangle305 radialPowerData9.radius
      (certifiedRadialHeight radialPowerData9 radialPowerData32)
      (certifiedRadialSlope radialPowerData9) 1 =
        planeArrayPolynomial majorizationArray305 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 6 2 majorizationTriangle305
    cellMatrix_6_2 cellMatrix_6_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf305_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray305 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf305_kernel {p : ℝ × ℝ} (hp : majorizationTriangle305.Contains p) :
    (1 : ℝ) ≤ kernel (((6 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 6 2 majorizationTriangle305
    radialPowerData9 radialPowerData32 radialPowerData9_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray305
    majorizationLeaf305_polynomial_eq majorizationLeaf305_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
