/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices22

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

/-- The actual closed rational triangle of majorization leaf 655. -/
def majorizationTriangle655 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 655. -/
def majorizationArray655 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2829395016280160012231708625234142397939394728299 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 2) then (39889871958337 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (1184529716437531 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-113518851619013175609762539271439701731931462313 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 2) then (4936317152357 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-141345698566541 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-121555824877051 /
    60000000000000000 : ℚ) else
  if p = (2, 2) then (16318687195549 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-73309467143693 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (30557369341391 /
    180000000000000000 : ℚ) else
  if p = (3, 2) then (-472146119891 /
    3000000000000000 : ℚ) else
  if p = (3, 3) then (10817590280863 /
    120000000000000000 : ℚ) else
  if p = (0, 1) then (-37435353980605954545976157421136458910631594211 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf655_polynomial_eq :
    lowerPullbackPolynomial 16 0 majorizationTriangle655 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray655 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 0 majorizationTriangle655
    cellMatrix_16_0 cellMatrix_16_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf655_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray655 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf655_kernel {p : ℝ × ℝ} (hp : majorizationTriangle655.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 0 majorizationTriangle655
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray655
    majorizationLeaf655_polynomial_eq majorizationLeaf655_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 656. -/
def majorizationTriangle656 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 656. -/
def majorizationArray656 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (54219717176761826334344566996765378227873802891 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (16260697768519399889740806592957967222476949123 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (203927154886421 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-351414036759887 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (51953641146403499558618143735356948475916735369 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-82132230211781 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (9061413720767 /
    12500000000000000 : ℚ) else
  if p = (1, 3) then (-20950129773497 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-503202858524327 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (4328664013119 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (543250749643 /
    4000000000000000 : ℚ) else
  if p = (2, 3) then (-22238596767313 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (-36909975138451 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-5318918748691 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (-13566926046949 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (10817590280863 /
    120000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf656_polynomial_eq :
    lowerPullbackPolynomial 16 0 majorizationTriangle656 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray656 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 0 majorizationTriangle656
    cellMatrix_16_0 cellMatrix_16_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf656_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray656 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf656_kernel {p : ℝ × ℝ} (hp : majorizationTriangle656.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 0 majorizationTriangle656
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray656
    majorizationLeaf656_polynomial_eq majorizationLeaf656_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 657. -/
def majorizationTriangle657 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 657. -/
def majorizationArray657 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (412572327075948409347154765684349783161226118269 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 1) then (-48452900259650698934862923006540106726643749769 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (84287297356947 /
    40000000000000000 : ℚ) else
  if p = (0, 3) then (-190967068527373 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (-50212712156857857141559966356929795557085303689 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-121600429957113 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-131473064261827 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (2211574565343 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-396985197580303 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-8034718361497 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-8134418550519 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (56841648866527 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (36909975138451 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-5318918748691 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (13566926046949 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (-55218289446817 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf657_polynomial_eq :
    lowerPullbackPolynomial 16 1 majorizationTriangle657 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray657 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 1 majorizationTriangle657
    cellMatrix_16_1 cellMatrix_16_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf657_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray657 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf657_kernel {p : ℝ × ℝ} (hp : majorizationTriangle657.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 1 majorizationTriangle657
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray657
    majorizationLeaf657_polynomial_eq majorizationLeaf657_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 658. -/
def majorizationTriangle658 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 658. -/
def majorizationArray658 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1895727426544857247766779291575170942547759539 /
    2852213850513516153367582212096000000000000000 : ℚ) else
  if p = (0, 1) then (28419635841174473657351546705875121464125100301 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-59134184297147 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (874842803842831 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (94255250155180870231597912518642297690898641703 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-444348256952657 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (135101176996823 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (3293814178483 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-1082400970944167 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (33899167167759 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-26432392544957 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (53594930027107 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-65944468757497 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-453970722533 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (14200649552963 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-55218289446817 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf658_polynomial_eq :
    lowerPullbackPolynomial 16 1 majorizationTriangle658 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray658 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 1 majorizationTriangle658
    cellMatrix_16_1 cellMatrix_16_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf658_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray658 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf658_kernel {p : ℝ × ℝ} (hp : majorizationTriangle658.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 1 majorizationTriangle658
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray658
    majorizationLeaf658_polynomial_eq majorizationLeaf658_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 659. -/
def majorizationTriangle659 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 659. -/
def majorizationArray659 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2173034299063247992025274356927840363228101917869 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-27768533952064646943374828455335520895666163981 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (15473705885867 /
    30000000000000000 : ℚ) else
  if p = (0, 3) then (-19635223115979 /
    50000000000000000 : ℚ) else
  if p = (1, 0) then (-90511505008660243282584537403664862036082897703 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-188955917392369 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-62419170282899 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-7700339957 /
    10000000000000000 : ℚ) else
  if p = (2, 0) then (-640117188608329 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-203357843751 /
    1250000000000000 : ℚ) else
  if p = (2, 2) then (4042389028483 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-5807648296759 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (65944468757497 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-453970722533 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-14200649552963 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (9280027519961 /
    225000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf659_polynomial_eq :
    lowerPullbackPolynomial 16 2 majorizationTriangle659 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray659 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 2 majorizationTriangle659
    cellMatrix_16_2 cellMatrix_16_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf659_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray659 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf659_kernel {p : ℝ × ℝ} (hp : majorizationTriangle659.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 2 majorizationTriangle659
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray659
    majorizationLeaf659_polynomial_eq majorizationLeaf659_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 660. -/
def majorizationTriangle660 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 660. -/
def majorizationArray660 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (41323969348220148387308305243284122834259493147 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (3218065619496893699998591798553059252070501899 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 2) then (-6381485814773 /
    4800000000000000 : ℚ) else
  if p = (0, 3) then (369275771274739 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (10952534975037582925263825623679924741691370017 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (-710464190745143 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (131014756795663 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (102160505029 /
    15000000000000000 : ℚ) else
  if p = (2, 0) then (-1224001319703181 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (47369621878539 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (12961937834177 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-19697165189567 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-28036408790543 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-12325589325689 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-31638271500799 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (9280027519961 /
    225000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf660_polynomial_eq :
    lowerPullbackPolynomial 16 2 majorizationTriangle660 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray660 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 2 majorizationTriangle660
    cellMatrix_16_2 cellMatrix_16_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf660_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray660 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf660_kernel {p : ℝ × ℝ} (hp : majorizationTriangle660.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 2 majorizationTriangle660
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray660
    majorizationLeaf660_polynomial_eq majorizationLeaf660_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 661. -/
def majorizationTriangle661 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 661. -/
def majorizationArray661 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (119361185217875219877969016519022537690350764533 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-9257737292021561570372351241432381524461709857 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (-24837119653619 /
    37500000000000000 : ℚ) else
  if p = (0, 3) then (-56152840232551 /
    90000000000000000 : ℚ) else
  if p = (1, 0) then (-10439892183262326079054110554937362530334370337 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (-314025268156877 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-62650180481609 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (9303652542227 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-170522920456987 /
    75000000000000000 : ℚ) else
  if p = (2, 1) then (-700880651057 /
    4000000000000000 : ℚ) else
  if p = (2, 2) then (-9338166833311 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (1524063461107 /
    37500000000000000 : ℚ) else
  if p = (3, 0) then (28036408790543 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-12325589325689 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (31638271500799 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-188138723181119 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf661_polynomial_eq :
    lowerPullbackPolynomial 16 3 majorizationTriangle661 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray661 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 3 majorizationTriangle661
    cellMatrix_16_3 cellMatrix_16_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf661_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray661 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf661_kernel {p : ℝ × ℝ} (hp : majorizationTriangle661.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 3 majorizationTriangle661
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray661
    majorizationLeaf661_polynomial_eq majorizationLeaf661_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 662. -/
def majorizationTriangle662 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 662. -/
def majorizationArray662 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2231226020157339076588943684532544303885527707 /
    4456584141427368989636847206400000000000000000 : ℚ) else
  if p = (0, 1) then (1532335334629780453803480714341129214435986017 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (0, 2) then (-240510297254863 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (1126396651192279 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (5236749170806304238636390123196283505520484131 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 1) then (-134330973324157 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (4663376781049 /
    4000000000000000 : ℚ) else
  if p = (1, 3) then (-102154082256787 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-745489039819837 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (23149931751699 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (-15079176996923 /
    20000000000000000 : ℚ) else
  if p = (2, 3) then (163753707803407 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-4990683648463 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-13718776950521 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (489063911501 /
    1875000000000000 : ℚ) else
  if p = (3, 3) then (-188138723181119 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf662_polynomial_eq :
    lowerPullbackPolynomial 16 3 majorizationTriangle662 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray662 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 3 majorizationTriangle662
    cellMatrix_16_3 cellMatrix_16_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf662_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray662 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf662_kernel {p : ℝ × ℝ} (hp : majorizationTriangle662.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 3 majorizationTriangle662
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray662
    majorizationLeaf662_polynomial_eq majorizationLeaf662_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 663. -/
def majorizationTriangle663 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 663. -/
def majorizationArray663 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (104515321860978714579659441482162130206228612513 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-4319159496361444636709759817909278543968018211 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (0, 2) then (-380112679777231 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-8332371683853 /
    12500000000000000 : ℚ) else
  if p = (1, 0) then (-4940442030071165348568387814167607686555574051 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 1) then (-420718324035641 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-8808575079431 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (-9715039336793 /
    75000000000000000 : ℚ) else
  if p = (2, 0) then (-7504797234683 /
    3000000000000000 : ℚ) else
  if p = (2, 1) then (-24005842254191 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (570868171109 /
    20000000000000000 : ℚ) else
  if p = (2, 3) then (-5734567429403 /
    20000000000000000 : ℚ) else
  if p = (3, 0) then (4990683648463 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-13718776950521 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (-489063911501 /
    1875000000000000 : ℚ) else
  if p = (3, 3) then (736169312880331 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf663_polynomial_eq :
    lowerPullbackPolynomial 16 4 majorizationTriangle663 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray663 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 4 majorizationTriangle663
    cellMatrix_16_4 cellMatrix_16_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf663_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray663 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf663_kernel {p : ℝ × ℝ} (hp : majorizationTriangle663.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 4 majorizationTriangle663
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray663
    majorizationLeaf663_polynomial_eq majorizationLeaf663_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 664. -/
def majorizationTriangle664 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 664. -/
def majorizationArray664 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (7542564167931954932172276274206701413279839883 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (24902805391962958265295198717432872591316755141 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-3137046600362707 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (1212964222323803 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (82643435355344278388451598992501401269534746703 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-1226610512276349 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-81206113369357 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (104791650807269 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-1934819461589899 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-77349296046189 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (413340520029011 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-564132289998241 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (44971327793111 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (95326880004827 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-193222953733337 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (736169312880331 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf664_polynomial_eq :
    lowerPullbackPolynomial 16 4 majorizationTriangle664 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray664 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 4 majorizationTriangle664
    cellMatrix_16_4 cellMatrix_16_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf664_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray664 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf664_kernel {p : ℝ × ℝ} (hp : majorizationTriangle664.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 4 majorizationTriangle664
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray664
    majorizationLeaf664_polynomial_eq majorizationLeaf664_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 665. -/
def majorizationTriangle665 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 665. -/
def majorizationArray665 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1445756821230841758707535616825471288746079375309 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-22987650070666022128250500006383498475052737221 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-680078060395939 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-77268709468337 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (-25575175821937510556444503399472115171780207301 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-547664232177123 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-82903032744327 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (63377156451937 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-899952739105283 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-52157835992073 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-166328341171 /
    200000000000000 : ℚ) else
  if p = (2, 3) then (96282850012269 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-44971327793111 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (95326880004827 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (193222953733337 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-1739120376958231 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf665_polynomial_eq :
    lowerPullbackPolynomial 16 5 majorizationTriangle665 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray665 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 5 majorizationTriangle665
    cellMatrix_16_5 cellMatrix_16_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf665_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray665 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf665_kernel {p : ℝ × ℝ} (hp : majorizationTriangle665.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 5 majorizationTriangle665
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray665
    majorizationLeaf665_polynomial_eq majorizationLeaf665_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 666. -/
def majorizationTriangle666 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 666. -/
def majorizationArray666 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2030393423664559842510448258371112108014827393 /
    5942112188569825319515796275200000000000000000 : ℚ) else
  if p = (0, 1) then (81011448310589165850438060152998190585571533021 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-305685495563007 /
    40000000000000000 : ℚ) else
  if p = (0, 3) then (724117916541199 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (28477947560400094273434357765448400283061220767 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-3133536213499121 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (1988131814592129 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-1034668963980743 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-1121097889069049 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (1996513317738637 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-2487203133813837 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (90641989182589 /
    18750000000000000 : ℚ) else
  if p = (3, 0) then (1016206233652319 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-2032922391501959 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (2898571892716451 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-1739120376958231 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf666_polynomial_eq :
    lowerPullbackPolynomial 16 5 majorizationTriangle666 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray666 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 16 5 majorizationTriangle666
    cellMatrix_16_5 cellMatrix_16_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf666_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray666 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf666_kernel {p : ℝ × ℝ} (hp : majorizationTriangle666.Contains p) :
    (0 : ℝ) ≤ kernel (((16 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 16 5 majorizationTriangle666
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray666
    majorizationLeaf666_polynomial_eq majorizationLeaf666_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
