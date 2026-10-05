/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices13

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

/-- The actual closed rational triangle of majorization leaf 543. -/
def majorizationTriangle543 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 543. -/
def majorizationArray543 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (325248338747986665287575411081315077525876323477 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-8906877928733 /
    3125000000000000 : ℚ) else
  if p = (0, 3) then (2354173083769 /
    900000000000000 : ℚ) else
  if p = (1, 0) then (-30029424788943734244757235253007079126217135959 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 2) then (5220605918391 /
    2500000000000000 : ℚ) else
  if p = (1, 3) then (-106012386748657 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-41551847859309 /
    10000000000000000 : ℚ) else
  if p = (2, 2) then (-5722839756753 /
    10000000000000000 : ℚ) else
  if p = (2, 3) then (39501611136137 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (48443237909407 /
    450000000000000000 : ℚ) else
  if p = (3, 2) then (27410210957021 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-87784858638103 /
    1800000000000000000 : ℚ) else
  if p = (0, 1) then (-33772576987797604655029911251471389801208485719 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf543_polynomial_eq :
    lowerPullbackPolynomial 12 0 majorizationTriangle543 radialPowerData12.radius
      (certifiedRadialHeight radialPowerData12 radialPowerData32)
      (certifiedRadialSlope radialPowerData12) 1 =
        planeArrayPolynomial majorizationArray543 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 0 majorizationTriangle543
    cellMatrix_12_0 cellMatrix_12_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf543_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray543 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf543_kernel {p : ℝ × ℝ} (hp : majorizationTriangle543.Contains p) :
    (1 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 0 majorizationTriangle543
    radialPowerData12 radialPowerData32 radialPowerData12_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray543
    majorizationLeaf543_polynomial_eq majorizationLeaf543_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 544. -/
def majorizationTriangle544 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 544. -/
def majorizationArray544 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (21013672484850968066114820081888623613587624341 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (1765262003923641061688698757737011695238873837 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (0, 2) then (2440632575663681 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-637271536211543 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (4899198043521670423569868542030968315450263751 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (15852864037891 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (164290984925747 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-135948763346983 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-2408025453677521 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (49051160535591 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (10585212685427 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-14044317181289 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (-90149786247217 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (21855985189981 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (10988145574687 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-87784858638103 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf544_polynomial_eq :
    lowerPullbackPolynomial 12 0 majorizationTriangle544 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray544 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 0 majorizationTriangle544
    cellMatrix_12_0 cellMatrix_12_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf544_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray544 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf544_kernel {p : ℝ × ℝ} (hp : majorizationTriangle544.Contains p) :
    (1 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 0 majorizationTriangle544
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray544
    majorizationLeaf544_polynomial_eq majorizationLeaf544_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 545. -/
def majorizationTriangle545 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 545. -/
def majorizationArray545 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (162374295192280872075732192028775591034467696957 /
    356526731314189519170947776512000000000000000000 : ℚ) else
  if p = (0, 1) then (-5315929892287473723892125460214578485138327751 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (0, 2) then (187389100326329 /
    37500000000000000 : ℚ) else
  if p = (0, 3) then (-251005616081803 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-1549108916650732309797900583830804577115538157 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (1, 1) then (99611313225309 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-109212923510331 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-6143319240497 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-669618703104793 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-17726786431393 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (2721853088093 /
    12500000000000000 : ℚ) else
  if p = (2, 3) then (-4773028025077 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (90149786247217 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (21855985189981 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-10988145574687 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (735634486093 /
    45000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf545_polynomial_eq :
    lowerPullbackPolynomial 12 1 majorizationTriangle545 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray545 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 1 majorizationTriangle545
    cellMatrix_12_1 cellMatrix_12_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf545_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray545 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf545_kernel {p : ℝ × ℝ} (hp : majorizationTriangle545.Contains p) :
    (1 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 1 majorizationTriangle545
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray545
    majorizationLeaf545_polynomial_eq majorizationLeaf545_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 546. -/
def majorizationTriangle546 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 546. -/
def majorizationArray546 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (126717918929020458603916365086995051415074171 /
    950737950171172051122527404032000000000000000 : ℚ) else
  if p = (0, 1) then (27757869178758529730520247365048823764703586041 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 2) then (269798996911971 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (164367718838371 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (26592619096363251851293041692059911901098092281 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (1, 1) then (-8342512377821 /
    6250000000000000 : ℚ) else
  if p = (1, 2) then (9096686567699 /
    10000000000000000 : ℚ) else
  if p = (1, 3) then (-17642746428233 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-209026416821627 /
    50000000000000000 : ℚ) else
  if p = (2, 1) then (1596804974531 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (6422877013479 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-15106295368489 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-266549383583131 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-14647508814421 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (3539057280341 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (735634486093 /
    45000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf546_polynomial_eq :
    lowerPullbackPolynomial 12 1 majorizationTriangle546 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray546 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 1 majorizationTriangle546
    cellMatrix_12_1 cellMatrix_12_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf546_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray546 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf546_kernel {p : ℝ × ℝ} (hp : majorizationTriangle546.Contains p) :
    (1 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 1 majorizationTriangle546
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray546
    majorizationLeaf546_polynomial_eq majorizationLeaf546_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 547. -/
def majorizationTriangle547 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 547. -/
def majorizationArray547 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (153339383610252201772341067731923048479918050611 /
    570442770102703230673516442419200000000000000000 : ℚ) else
  if p = (0, 1) then (-9170520987624712652878624975055607437203366483 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (0, 2) then (449041751395171 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (-160304614248539 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (-1661220763223726500533891088766877383966384247 /
    12676506002282294014967032053760000000000000000 : ℚ) else
  if p = (1, 1) then (-256059025312197 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-236855804742153 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (648650088523 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-554973277088531 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (1873069018173 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (29230565334257 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (5574941328389 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (266549383583131 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-14647508814421 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-3539057280341 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-42717778140679 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf547_polynomial_eq :
    lowerPullbackPolynomial 12 2 majorizationTriangle547 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray547 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 2 majorizationTriangle547
    cellMatrix_12_2 cellMatrix_12_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf547_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray547 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf547_kernel {p : ℝ × ℝ} (hp : majorizationTriangle547.Contains p) :
    (1 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 2 majorizationTriangle547
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray547
    majorizationLeaf547_polynomial_eq majorizationLeaf547_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 548. -/
def majorizationTriangle548 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 548. -/
def majorizationArray548 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (11097153282331994954501426966493822716943313 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (364439833650641131 /
    3000000000000000000 : ℚ) else
  if p = (0, 2) then (726273163344329 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (892520818127497 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (364373809498586101 /
    3000000000000000000 : ℚ) else
  if p = (1, 1) then (-120550888093421 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (153860313022853 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (28073418331127 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-495766785451373 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (-29340446141239 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (16423377883571 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (1853626034069 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (-28211984526361 /
    300000000000000000 : ℚ) else
  if p = (3, 1) then (-10740566919297 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (770947257017 /
    10000000000000000 : ℚ) else
  if p = (3, 3) then (-42717778140679 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf548_polynomial_eq :
    lowerPullbackPolynomial 12 2 majorizationTriangle548 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray548 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 2 majorizationTriangle548
    cellMatrix_12_2 cellMatrix_12_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf548_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray548 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf548_kernel {p : ℝ × ℝ} (hp : majorizationTriangle548.Contains p) :
    (1 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 2 majorizationTriangle548
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray548
    majorizationLeaf548_polynomial_eq majorizationLeaf548_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 549. -/
def majorizationTriangle549 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 549. -/
def majorizationArray549 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (41852008174072112086100289878792282724765502229 /
    356526731314189519170947776512000000000000000000 : ℚ) else
  if p = (0, 1) then (-354636193343937061 /
    3000000000000000000 : ℚ) else
  if p = (0, 2) then (1283381071484621 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-1044214870315927 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-112913036896742207 /
    1000000000000000000 : ℚ) else
  if p = (1, 1) then (-145175746853073 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-46592780842203 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (84049290478639 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-2648105834415031 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (93783847657021 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (62680213304591 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-1177573115537 /
    15000000000000000 : ℚ) else
  if p = (3, 0) then (28211984526361 /
    300000000000000000 : ℚ) else
  if p = (3, 1) then (-10740566919297 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (-770947257017 /
    10000000000000000 : ℚ) else
  if p = (3, 3) then (34443181463749 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf549_polynomial_eq :
    lowerPullbackPolynomial 12 3 majorizationTriangle549 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray549 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 3 majorizationTriangle549
    cellMatrix_12_3 cellMatrix_12_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf549_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray549 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf549_kernel {p : ℝ × ℝ} (hp : majorizationTriangle549.Contains p) :
    (1 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 3 majorizationTriangle549
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray549
    majorizationLeaf549_polynomial_eq majorizationLeaf549_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 550. -/
def majorizationTriangle550 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 550. -/
def majorizationArray550 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (31646951429784138261262224296021864713265925739 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (99849892773206814819973218038852907469075782313 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-482363213408191 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (1690999590160711 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (34292057099435453034879658307474402073824856291 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-100267394166843 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (22762199922393 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (108335913178067 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1177101099170083 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-990549175013 /
    4000000000000000 : ℚ) else
  if p = (2, 2) then (47045434073 /
    2500000000000000 : ℚ) else
  if p = (2, 3) then (12659743157731 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (128385622188491 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-122513890894073 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (11813653957271 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (34443181463749 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf550_polynomial_eq :
    lowerPullbackPolynomial 12 3 majorizationTriangle550 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray550 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 3 majorizationTriangle550
    cellMatrix_12_3 cellMatrix_12_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf550_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray550 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf550_kernel {p : ℝ × ℝ} (hp : majorizationTriangle550.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 3 majorizationTriangle550
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray550
    majorizationLeaf550_polynomial_eq majorizationLeaf550_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 551. -/
def majorizationTriangle551 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 551. -/
def majorizationArray551 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (314377435172749227791206438714442512040457075411 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-31869067639676711441512026935300541099493689571 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-268349556382411 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-826342200147419 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-95618841862629931751513303726436209058650397353 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-1023707961730117 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-64865323253737 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (75642245958249 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-29677554348689 /
    8000000000000000 : ℚ) else
  if p = (2, 1) then (172041349644723 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (15577288683111 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-11811498061703 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-128385622188491 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-122513890894073 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-11813653957271 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (4180376325833 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf551_polynomial_eq :
    lowerPullbackPolynomial 12 4 majorizationTriangle551 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray551 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 4 majorizationTriangle551
    cellMatrix_12_4 cellMatrix_12_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf551_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray551 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf551_kernel {p : ℝ × ℝ} (hp : majorizationTriangle551.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 4 majorizationTriangle551
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray551
    majorizationLeaf551_polynomial_eq majorizationLeaf551_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 552. -/
def majorizationTriangle552 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 552. -/
def majorizationArray552 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (56128202928276507049451345967922252144104467083 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (46320698691927909729057536662013090870115324809 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-2860915543538059 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (1896189116721677 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (46687351131361328263599067414529171450511643529 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-728769450868121 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-118894102311409 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (32883700431239 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-2221402659444139 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-29980986668887 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-23310106807603 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (27073741533443 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (523007504090857 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-137780446156949 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (690580261121 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (4180376325833 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf552_polynomial_eq :
    lowerPullbackPolynomial 12 4 majorizationTriangle552 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray552 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 4 majorizationTriangle552
    cellMatrix_12_4 cellMatrix_12_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf552_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray552 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf552_kernel {p : ℝ × ℝ} (hp : majorizationTriangle552.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 4 majorizationTriangle552
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray552
    majorizationLeaf552_polynomial_eq majorizationLeaf552_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 553. -/
def majorizationTriangle553 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 553. -/
def majorizationArray553 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (419253517222518416804182327798902945291517543549 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 1) then (-14802701895648422147658460493955678627173811843 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (-109469175652983 /
    20000000000000000 : ℚ) else
  if p = (0, 3) then (-10492239689057 /
    28125000000000000 : ℚ) else
  if p = (1, 0) then (-43581767348423045314622879620647583691262808969 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-231627967590711 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (16206141462101 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (404914117363 /
    2500000000000000 : ℚ) else
  if p = (2, 0) then (-283065859225547 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (41940358206459 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-9928602750999 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (1930270117711 /
    60000000000000000 : ℚ) else
  if p = (3, 0) then (-523007504090857 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-137780446156949 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-690580261121 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (-78371649671329 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf553_polynomial_eq :
    lowerPullbackPolynomial 12 5 majorizationTriangle553 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray553 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 5 majorizationTriangle553
    cellMatrix_12_5 cellMatrix_12_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf553_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray553 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf553_kernel {p : ℝ × ℝ} (hp : majorizationTriangle553.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 5 majorizationTriangle553
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray553
    majorizationLeaf553_polynomial_eq majorizationLeaf553_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 554. -/
def majorizationTriangle554 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 554. -/
def majorizationArray554 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (49252735820133667728955761476136253764968462971 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (91236066244208949949953263980446241783865226023 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-1630672132638173 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (44492080193143 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (85076446661989161969099823894758173177696301863 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-108392026348823 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (-8815362158071 /
    10000000000000000 : ℚ) else
  if p = (1, 3) then (57413140850011 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1130229484177253 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (37854087720269 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-41189527650911 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (19689649498073 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (128134899518731 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (-3485279663117 /
    9375000000000000 : ℚ) else
  if p = (3, 2) then (40912275488467 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-78371649671329 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf554_polynomial_eq :
    lowerPullbackPolynomial 12 5 majorizationTriangle554 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray554 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 5 majorizationTriangle554
    cellMatrix_12_5 cellMatrix_12_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf554_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray554 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf554_kernel {p : ℝ × ℝ} (hp : majorizationTriangle554.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 5 majorizationTriangle554
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray554
    majorizationLeaf554_polynomial_eq majorizationLeaf554_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
