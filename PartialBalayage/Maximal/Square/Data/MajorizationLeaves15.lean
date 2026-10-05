/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices15

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

/-- The actual closed rational triangle of majorization leaf 567. -/
def majorizationTriangle567 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 567. -/
def majorizationArray567 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (71600720546540380840200896045508676338383351707 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (24949723155787724011991822096735990097694653991 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (8895927032242849 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (-446995836444133 /
    6250000000000000 : ℚ) else
  if p = (1, 0) then (24949723155787724011991822096735990097694653991 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-3105985205593813 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (4351529446503707 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (-307171286887283 /
    12500000000000000 : ℚ) else
  if p = (2, 0) then (8895927032242849 /
    75000000000000000 : ℚ) else
  if p = (2, 1) then (4351529446503707 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-3243492127491071 /
    10000000000000000 : ℚ) else
  if p = (2, 3) then (2988689694855577 /
    20000000000000000 : ℚ) else
  if p = (3, 0) then (-446995836444133 /
    6250000000000000 : ℚ) else
  if p = (3, 1) then (-307171286887283 /
    12500000000000000 : ℚ) else
  if p = (3, 2) then (2988689694855577 /
    20000000000000000 : ℚ) else
  if p = (3, 3) then (-128177911297148767 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf567_polynomial_eq :
    lowerPullbackPolynomial 12 12 majorizationTriangle567 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray567 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 12 majorizationTriangle567
    cellMatrix_12_12 cellMatrix_12_12_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf567_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray567 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf567_kernel {p : ℝ × ℝ} (hp : majorizationTriangle567.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((12 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 12 majorizationTriangle567
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray567
    majorizationLeaf567_polynomial_eq majorizationLeaf567_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 568. -/
def majorizationTriangle568 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 568. -/
def majorizationArray568 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1110831262182247539785394311559284397163607797 /
    14261069252567580766837911060480000000000000000 : ℚ) else
  if p = (0, 1) then (11175399501737017117877060848106845042746135367 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-13726372155635567 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (32163304967825893 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (11175399501737017117877060848106845042746135367 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-13726372155635567 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-13726372155635567 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (36399248623596269 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-13726372155635567 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-13726372155635567 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-13726372155635567 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (38517220451481457 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (32163304967825893 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (36399248623596269 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (38517220451481457 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-128177911297148767 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf568_polynomial_eq :
    lowerPullbackPolynomial 12 12 majorizationTriangle568 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray568 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 12 12 majorizationTriangle568
    cellMatrix_12_12 cellMatrix_12_12_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf568_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray568 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf568_kernel {p : ℝ × ℝ} (hp : majorizationTriangle568.Contains p) :
    (0 : ℝ) ≤ kernel (((12 : ℝ) + p.1) / 16) (((12 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 12 12 majorizationTriangle568
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray568
    majorizationLeaf568_polynomial_eq majorizationLeaf568_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 574. -/
def majorizationTriangle574 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 574. -/
def majorizationArray574 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (169436922662614553337108788802374355079535575357 /
    356526731314189519170947776512000000000000000000 : ℚ) else
  if p = (0, 2) then (-372862552697017 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (637271536211543 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (-4915183297106939976644824473760169854998710471 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 2) then (121777652557601 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-135948763346983 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-143708619995057 /
    37500000000000000 : ℚ) else
  if p = (2, 2) then (-29818186610509 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (14044317181289 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (2434410326691 /
    10000000000000000 : ℚ) else
  if p = (3, 2) then (1550832497743 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-4147458994429 /
    900000000000000000 : ℚ) else
  if p = (0, 1) then (-1793237921528050279121903612119695394300592877 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf574_polynomial_eq :
    lowerPullbackPolynomial 13 0 majorizationTriangle574 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray574 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 0 majorizationTriangle574
    cellMatrix_13_0 cellMatrix_13_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf574_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray574 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf574_kernel {p : ℝ × ℝ} (hp : majorizationTriangle574.Contains p) :
    (1 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 0 majorizationTriangle574
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray574
    majorizationLeaf574_polynomial_eq majorizationLeaf574_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 575. -/
def majorizationTriangle575 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 575. -/
def majorizationArray575 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1103346878099387968839951891550072201188627201 /
    7922816251426433759354395033600000000000000000 : ℚ) else
  if p = (0, 1) then (29012359032416833639714838637361654835883353849 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 2) then (660175111980107 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-433037730133069 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (9295790080435452274505087816413015554943378003 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (1, 1) then (-8522928897669 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (142110482557293 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-91899345405639 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-5200564074407 /
    1600000000000000 : ℚ) else
  if p = (2, 1) then (38736088551533 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (11595289683027 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-61926667917587 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-28613370360931 /
    112500000000000000 : ℚ) else
  if p = (3, 1) then (5157535992029 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-1262596247 /
    750000000000000 : ℚ) else
  if p = (3, 3) then (-4147458994429 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf575_polynomial_eq :
    lowerPullbackPolynomial 13 0 majorizationTriangle575 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray575 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 0 majorizationTriangle575
    cellMatrix_13_0 cellMatrix_13_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf575_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray575 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf575_kernel {p : ℝ × ℝ} (hp : majorizationTriangle575.Contains p) :
    (1 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 0 majorizationTriangle575
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray575
    majorizationLeaf575_polynomial_eq majorizationLeaf575_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 576. -/
def majorizationTriangle576 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 576. -/
def majorizationArray576 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (6444154352487453031325846839165296410327396651 /
    22817710804108129226940657696768000000000000000 : ℚ) else
  if p = (0, 1) then (-9681450935564113262124170723462855699208102483 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (0, 2) then (2440632575663681 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-164367718838371 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (-5301237961979424422559330938167227953583923557 /
    38029518006846882044901096161280000000000000000 : ℚ) else
  if p = (1, 1) then (15852864037891 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-164290984925747 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-17642746428233 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-2408025453677521 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-49051160535591 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (10585212685427 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (15106295368489 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (28613370360931 /
    112500000000000000 : ℚ) else
  if p = (3, 1) then (5157535992029 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (1262596247 /
    750000000000000 : ℚ) else
  if p = (3, 3) then (-4147099678501 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf576_polynomial_eq :
    lowerPullbackPolynomial 13 1 majorizationTriangle576 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray576 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 1 majorizationTriangle576
    cellMatrix_13_1 cellMatrix_13_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf576_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray576 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf576_kernel {p : ℝ × ℝ} (hp : majorizationTriangle576.Contains p) :
    (1 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 1 majorizationTriangle576
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray576
    majorizationLeaf576_polynomial_eq majorizationLeaf576_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 577. -/
def majorizationTriangle577 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 577. -/
def majorizationArray577 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (3923948946203478275337049358978913733861019 /
    23768448754279301278063185100800000000000000000 : ℚ) else
  if p = (0, 1) then (95095614444173359 /
    750000000000000000 : ℚ) else
  if p = (0, 2) then (37816299661841 /
    20000000000000000 : ℚ) else
  if p = (0, 3) then (94004038453899 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (190243964913571933 /
    1500000000000000000 : ℚ) else
  if p = (1, 1) then (-148381224208757 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (18266129620319 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (-4018554405259 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-338852671308943 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (8513806265497 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (1264148292189 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (98806889701 /
    40000000000000000 : ℚ) else
  if p = (3, 0) then (-26400054111437 /
    100000000000000000 : ℚ) else
  if p = (3, 1) then (-2126586367373 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (1298193476367 /
    50000000000000000 : ℚ) else
  if p = (3, 3) then (-4147099678501 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf577_polynomial_eq :
    lowerPullbackPolynomial 13 1 majorizationTriangle577 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray577 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 1 majorizationTriangle577
    cellMatrix_13_1 cellMatrix_13_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf577_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray577 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf577_kernel {p : ℝ × ℝ} (hp : majorizationTriangle577.Contains p) :
    (1 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 1 majorizationTriangle577
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray577
    majorizationLeaf577_polynomial_eq majorizationLeaf577_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 578. -/
def majorizationTriangle578 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 578. -/
def majorizationArray578 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (14658224979935739560689693447657241429951109383 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 1) then (-188082584687360953 /
    1500000000000000000 : ℚ) else
  if p = (0, 2) then (269798996911971 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (-892520818127497 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-89445191169644489 /
    750000000000000000 : ℚ) else
  if p = (1, 1) then (-8342512377821 /
    6250000000000000 : ℚ) else
  if p = (1, 2) then (-9096686567699 /
    10000000000000000 : ℚ) else
  if p = (1, 3) then (28073418331127 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-209026416821627 /
    50000000000000000 : ℚ) else
  if p = (2, 1) then (-1596804974531 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (6422877013479 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-1853626034069 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (26400054111437 /
    100000000000000000 : ℚ) else
  if p = (3, 1) then (-2126586367373 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-1298193476367 /
    50000000000000000 : ℚ) else
  if p = (3, 3) then (8475998245073 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf578_polynomial_eq :
    lowerPullbackPolynomial 13 2 majorizationTriangle578 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray578 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 2 majorizationTriangle578
    cellMatrix_13_2 cellMatrix_13_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf578_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray578 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf578_kernel {p : ℝ × ℝ} (hp : majorizationTriangle578.Contains p) :
    (1 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 2 majorizationTriangle578
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray578
    majorizationLeaf578_polynomial_eq majorizationLeaf578_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 579. -/
def majorizationTriangle579 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 579. -/
def majorizationArray579 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (31499180513910862007832600277852458762739437163 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (102240559060892432891794950257547830775446117033 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (19178752153447 /
    37500000000000000 : ℚ) else
  if p = (0, 3) then (413814477700039 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (106634718912064527417159625151878190542100765353 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-142751841526777 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (64057940363521 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (1801315623551 /
    60000000000000000 : ℚ) else
  if p = (2, 0) then (-128415714897461 /
    37500000000000000 : ℚ) else
  if p = (2, 1) then (-1203314109379 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (116513180153 /
    2500000000000000 : ℚ) else
  if p = (2, 3) then (99016490659 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (-424182488897489 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-26933817922481 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (7102323471331 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (8475998245073 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf579_polynomial_eq :
    lowerPullbackPolynomial 13 2 majorizationTriangle579 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray579 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 2 majorizationTriangle579
    cellMatrix_13_2 cellMatrix_13_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf579_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray579 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf579_kernel {p : ℝ × ℝ} (hp : majorizationTriangle579.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 2 majorizationTriangle579
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray579
    majorizationLeaf579_polynomial_eq majorizationLeaf579_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 580. -/
def majorizationTriangle580 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 580. -/
def majorizationArray580 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2829399278381630818134124449990699144965398122859 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-99472048494998404677112015117941420493956586153 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (726273163344329 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-1690999590160711 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-99451124606002875010805553411967671539320625833 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-120550888093421 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-153860313022853 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (108335913178067 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-495766785451373 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (29340446141239 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (16423377883571 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-12659743157731 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (424182488897489 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-26933817922481 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-7102323471331 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-63214650833 /
    120000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf580_polynomial_eq :
    lowerPullbackPolynomial 13 3 majorizationTriangle580 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray580 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 3 majorizationTriangle580
    cellMatrix_13_3 cellMatrix_13_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf580_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray580 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf580_kernel {p : ℝ × ℝ} (hp : majorizationTriangle580.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 3 majorizationTriangle580
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray580
    majorizationLeaf580_polynomial_eq majorizationLeaf580_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 581. -/
def majorizationTriangle581 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 581. -/
def majorizationArray581 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (3721596034373641340920772394364740050031129029 /
    4753689750855860255612637020160000000000000000 : ℚ) else
  if p = (0, 1) then (15037299536931524714079455124854450351500478083 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (-183009877567841 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (702459649931099 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (48278812297906912328687328859289858655079256969 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-372585460230541 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (11511918406733 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (2735606903337 /
    20000000000000000 : ℚ) else
  if p = (2, 0) then (-42355757362221 /
    12500000000000000 : ℚ) else
  if p = (2, 1) then (-1860193530753 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-2143454253993 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (6803981460113 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-160562922476779 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-21043342313819 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (4025271616913 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-63214650833 /
    120000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf581_polynomial_eq :
    lowerPullbackPolynomial 13 3 majorizationTriangle581 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray581 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 3 majorizationTriangle581
    cellMatrix_13_3 cellMatrix_13_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf581_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray581 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf581_kernel {p : ℝ × ℝ} (hp : majorizationTriangle581.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 3 majorizationTriangle581
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray581
    majorizationLeaf581_polynomial_eq majorizationLeaf581_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 582. -/
def majorizationTriangle582 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 582. -/
def majorizationArray582 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1256228517987597367063718923717313138992006516087 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-43289712854441588901839247626753185737904903049 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-482363213408191 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-1896189116721677 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-14934284038997120348057375356179445038034765443 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (-100267394166843 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (-22762199922393 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (32883700431239 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-1177101099170083 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (990549175013 /
    4000000000000000 : ℚ) else
  if p = (2, 2) then (47045434073 /
    2500000000000000 : ℚ) else
  if p = (2, 3) then (-27073741533443 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (160562922476779 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-21043342313819 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-4025271616913 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-28690378751 /
    3000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf582_polynomial_eq :
    lowerPullbackPolynomial 13 4 majorizationTriangle582 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray582 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 4 majorizationTriangle582
    cellMatrix_13_4 cellMatrix_13_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf582_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray582 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf582_kernel {p : ℝ × ℝ} (hp : majorizationTriangle582.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 4 majorizationTriangle582
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray582
    majorizationLeaf582_polynomial_eq majorizationLeaf582_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 583. -/
def majorizationTriangle583 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 583. -/
def majorizationArray583 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (49295682475068860804604983129105736439446977147 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (84976261138320193272346114489017453981146362663 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-2599428327511067 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (1501369062104021 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (89064938903286732519741007212540888019930526503 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-744209475876237 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-47009118211777 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (31018930612903 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-2067902725325573 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (45421011677003 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-48574877292029 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (44287968784043 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-76749967059283 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-2513399944863 /
    20000000000000000 : ℚ) else
  if p = (3, 2) then (12632385242213 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-28690378751 /
    3000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf583_polynomial_eq :
    lowerPullbackPolynomial 13 4 majorizationTriangle583 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray583 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 4 majorizationTriangle583
    cellMatrix_13_4 cellMatrix_13_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf583_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray583 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf583_kernel {p : ℝ × ℝ} (hp : majorizationTriangle583.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 4 majorizationTriangle583
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray583
    majorizationLeaf583_polynomial_eq majorizationLeaf583_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
