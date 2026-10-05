/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices24

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

/-- The actual closed rational triangle of majorization leaf 678. -/
def majorizationTriangle678 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 678. -/
def majorizationArray678 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1232122598535836556048681187630484574091443654007 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 2) then (11288054602591 /
    60000000000000000 : ℚ) else
  if p = (0, 3) then (351414036759887 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-51808220784508847315363629847505918406044832649 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 2) then (-1928184089129 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (-20950129773497 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-4549922776783 /
    3000000000000000 : ℚ) else
  if p = (2, 2) then (-30895924793551 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (22238596767313 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (11075110010261 /
    180000000000000000 : ℚ) else
  if p = (3, 2) then (15317732830121 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (-3301958672851 /
    50000000000000000 : ℚ) else
  if p = (0, 1) then (-16505932479582371103605624913010473456438134403 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf678_polynomial_eq :
    lowerPullbackPolynomial 17 0 majorizationTriangle678 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray678 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 0 majorizationTriangle678
    cellMatrix_17_0 cellMatrix_17_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf678_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray678 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf678_kernel {p : ℝ × ℝ} (hp : majorizationTriangle678.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 0 majorizationTriangle678
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray678
    majorizationLeaf678_polynomial_eq majorizationLeaf678_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 679. -/
def majorizationTriangle679 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 679. -/
def majorizationArray679 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (46742525357148989313294707537194140786037439099 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (87397409370749643440093179854353991908222120743 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (202324396246583 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-118429596645487 /
    450000000000000000 : ℚ) else
  if p = (1, 0) then (95711873003454553415959874162499101439677772583 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-114925867107567 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (37064281367531 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (-33331258362557 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-207678083801807 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (1547898084331 /
    10000000000000000 : ℚ) else
  if p = (2, 2) then (-15218521710001 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (3739515644173 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (-87846690920713 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (917837604583 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (7199947612769 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (-3301958672851 /
    50000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf679_polynomial_eq :
    lowerPullbackPolynomial 17 0 majorizationTriangle679 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray679 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 0 majorizationTriangle679
    cellMatrix_17_0 cellMatrix_17_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf679_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray679 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf679_kernel {p : ℝ × ℝ} (hp : majorizationTriangle679.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 0 majorizationTriangle679
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray679
    majorizationLeaf679_polynomial_eq majorizationLeaf679_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 680. -/
def majorizationTriangle680 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 680. -/
def majorizationArray680 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2152609287306354831277178644713076019783088782509 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-28819249189907865993900163302845880750422823181 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (203927154886421 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-874842803842831 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-92800843251414197760491937821503735868240245543 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-82132230211781 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-9061413720767 /
    12500000000000000 : ℚ) else
  if p = (1, 3) then (3293814178483 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-503202858524327 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-4328664013119 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (543250749643 /
    4000000000000000 : ℚ) else
  if p = (2, 3) then (-53594930027107 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (87846690920713 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (917837604583 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (-7199947612769 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (100299143721481 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf680_polynomial_eq :
    lowerPullbackPolynomial 17 1 majorizationTriangle680 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray680 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 1 majorizationTriangle680
    cellMatrix_17_1 cellMatrix_17_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf680_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray680 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf680_kernel {p : ℝ × ℝ} (hp : majorizationTriangle680.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 1 majorizationTriangle680
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray680
    majorizationLeaf680_polynomial_eq majorizationLeaf680_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 681. -/
def majorizationTriangle681 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 681. -/
def majorizationArray681 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (40561417609183788222919475826048654809462554907 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (3256963414048315803302919831501393020948827659 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 2) then (-250517665051579 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (75473676883027 /
    150000000000000000 : ℚ) else
  if p = (1, 0) then (3671730342529440574356581457094230562819788299 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (1, 1) then (-261687629476333 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (9079149954213 /
    12500000000000000 : ℚ) else
  if p = (1, 3) then (747681550679 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-12102414210409 /
    7500000000000000 : ℚ) else
  if p = (2, 1) then (180511339329 /
    800000000000000 : ℚ) else
  if p = (2, 2) then (4066792568593 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-7784035615729 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-38069278037149 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-3742889221497 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-14233187606443 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (100299143721481 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf681_polynomial_eq :
    lowerPullbackPolynomial 17 1 majorizationTriangle681 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray681 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 1 majorizationTriangle681
    cellMatrix_17_1 cellMatrix_17_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf681_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray681 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf681_kernel {p : ℝ × ℝ} (hp : majorizationTriangle681.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 1 majorizationTriangle681
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray681
    majorizationLeaf681_polynomial_eq majorizationLeaf681_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 682. -/
def majorizationTriangle682 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 682. -/
def majorizationArray682 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (117627364356327055400856639529451832230199837173 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-3161495396858930118874945886848076801300745739 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 2) then (-59134184297147 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-369275771274739 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-10609029019533971514067746710671347066217654817 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (-444348256952657 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-135101176996823 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (102160505029 /
    15000000000000000 : ℚ) else
  if p = (2, 0) then (-1082400970944167 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-33899167167759 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-26432392544957 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (19697165189567 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (38069278037149 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-3742889221497 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (14233187606443 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-186578084352841 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf682_polynomial_eq :
    lowerPullbackPolynomial 17 2 majorizationTriangle682 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray682 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 2 majorizationTriangle682
    cellMatrix_17_2 cellMatrix_17_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf682_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray682 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf682_kernel {p : ℝ × ℝ} (hp : majorizationTriangle682.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 2 majorizationTriangle682
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray682
    majorizationLeaf682_polynomial_eq majorizationLeaf682_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 683. -/
def majorizationTriangle683 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 683. -/
def majorizationArray683 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2182215219391725257979511947851918403924208283 /
    4456584141427368989636847206400000000000000000 : ℚ) else
  if p = (0, 1) then (4563744135572617879522397798550049864608980771 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (0, 2) then (-259144541052919 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (264895791720479 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (5216879666625487071149351696581069067735867171 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 1) then (-183522212176179 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (248969402660821 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-103703003393413 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1201958884480061 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (159777248257213 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-26183316739867 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (49061251324569 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-275530440289 /
    22500000000000000 : ℚ) else
  if p = (3, 1) then (-56203813189337 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (17984815191689 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (-186578084352841 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf683_polynomial_eq :
    lowerPullbackPolynomial 17 2 majorizationTriangle683 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray683 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 2 majorizationTriangle683
    cellMatrix_17_2 cellMatrix_17_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf683_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray683 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf683_kernel {p : ℝ × ℝ} (hp : majorizationTriangle683.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 2 majorizationTriangle683
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray683
    majorizationLeaf683_polynomial_eq majorizationLeaf683_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 684. -/
def majorizationTriangle684 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 684. -/
def majorizationArray684 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (102579956071613949106986666552682807239603783073 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-1442485048904775472716026537277979937877199457 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (0, 2) then (-6381485814773 /
    4800000000000000 : ℚ) else
  if p = (0, 3) then (-1126396651192279 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-4976624204987777330782104725844313306371530531 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 1) then (-710464190745143 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-131014756795663 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-102154082256787 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1224001319703181 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-47369621878539 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (12961937834177 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-163753707803407 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (275530440289 /
    22500000000000000 : ℚ) else
  if p = (3, 1) then (-56203813189337 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-17984815191689 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (110440995485249 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf684_polynomial_eq :
    lowerPullbackPolynomial 17 3 majorizationTriangle684 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray684 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 3 majorizationTriangle684
    cellMatrix_17_3 cellMatrix_17_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf684_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray684 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf684_kernel {p : ℝ × ℝ} (hp : majorizationTriangle684.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 3 majorizationTriangle684
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray684
    majorizationLeaf684_polynomial_eq majorizationLeaf684_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 685. -/
def majorizationTriangle685 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 685. -/
def majorizationArray685 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2458229341889303613802684286012667538005507289 /
    5942112188569825319515796275200000000000000000 : ℚ) else
  if p = (0, 1) then (24087247293239231701379710435135104015952782021 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-426199458954327 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (1261474048461367 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (81783098751577129851740139642555571973693139023 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-295641347788661 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (1951285109 /
    24414062500000 : ℚ) else
  if p = (1, 3) then (77661491682631 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-262524685873603 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (-19320462363051 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (22998480088047 /
    12500000000000000 : ℚ) else
  if p = (2, 3) then (-498892265108087 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (10521254450243 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (21873441955483 /
    50000000000000000 : ℚ) else
  if p = (3, 2) then (-259383725688991 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (110440995485249 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf685_polynomial_eq :
    lowerPullbackPolynomial 17 3 majorizationTriangle685 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray685 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 3 majorizationTriangle685
    cellMatrix_17_3 cellMatrix_17_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf685_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray685 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf685_kernel {p : ℝ × ℝ} (hp : majorizationTriangle685.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 3 majorizationTriangle685
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray685
    majorizationLeaf685_polynomial_eq majorizationLeaf685_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 686. -/
def majorizationTriangle686 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 686. -/
def majorizationArray686 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1417944987655283163938974656448066831061806960589 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-22229579063919921739147356799783517817674146501 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-240510297254863 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (-1212964222323803 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-76924627862431171253057238082116887248422856783 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-134330973324157 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (-4663376781049 /
    4000000000000000 : ℚ) else
  if p = (1, 3) then (104791650807269 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-745489039819837 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-23149931751699 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (-15079176996923 /
    20000000000000000 : ℚ) else
  if p = (2, 3) then (564132289998241 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-10521254450243 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (21873441955483 /
    50000000000000000 : ℚ) else
  if p = (3, 2) then (259383725688991 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-369268295507237 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf686_polynomial_eq :
    lowerPullbackPolynomial 17 4 majorizationTriangle686 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray686 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 4 majorizationTriangle686
    cellMatrix_17_4 cellMatrix_17_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf686_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray686 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf686_kernel {p : ℝ × ℝ} (hp : majorizationTriangle686.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 4 majorizationTriangle686
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray686
    majorizationLeaf686_polynomial_eq majorizationLeaf686_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 687. -/
def majorizationTriangle687 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 687. -/
def majorizationArray687 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5981924391536435438167062871719507207855662723 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (77444363611507670715881422119556900564089528541 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-2229026954177377 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (237607144328599 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (84527355607432434095128673913538380815398953181 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-193456898345459 /
    12500000000000000 : ℚ) else
  if p = (1, 2) then (474190013689943 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (-470193781786711 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-1499328946112821 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (60814036165537 /
    6250000000000000 : ℚ) else
  if p = (2, 2) then (-119565334407907 /
    10000000000000000 : ℚ) else
  if p = (2, 3) then (689820592391723 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (1063838430635743 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-2023398453343373 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (2804647208187151 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-369268295507237 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf687_polynomial_eq :
    lowerPullbackPolynomial 17 4 majorizationTriangle687 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray687 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 4 majorizationTriangle687
    cellMatrix_17_4 cellMatrix_17_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf687_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray687 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf687_kernel {p : ℝ × ℝ} (hp : majorizationTriangle687.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 4 majorizationTriangle687
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray687
    majorizationLeaf687_polynomial_eq majorizationLeaf687_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 688. -/
def majorizationTriangle688 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 688. -/
def majorizationArray688 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1198120999460957472724047726441228814439849145463 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-22924976505668740408465282023523937990545012127 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-3137046600362707 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-724117916541199 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-76709948696461624817961848910774597467219517661 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-1226610512276349 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (81206113369357 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-1034668963980743 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-1934819461589899 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (77349296046189 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (413340520029011 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-90641989182589 /
    18750000000000000 : ℚ) else
  if p = (3, 0) then (-1063838430635743 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-2023398453343373 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-2804647208187151 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (6747378935996557 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf688_polynomial_eq :
    lowerPullbackPolynomial 17 5 majorizationTriangle688 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray688 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 5 majorizationTriangle688
    cellMatrix_17_5 cellMatrix_17_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf688_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray688 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf688_kernel {p : ℝ × ℝ} (hp : majorizationTriangle688.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 5 majorizationTriangle688
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray688
    majorizationLeaf688_polynomial_eq majorizationLeaf688_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 689. -/
def majorizationTriangle689 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 689. -/
def majorizationArray689 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (17674121856178281001914417998326808260834881059 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (7578922962102489331125496016335980004573718561 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (0, 2) then (-91514707685713 /
    7500000000000000 : ℚ) else
  if p = (0, 3) then (477187117750381 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (23545943741249914633466221352332462682993096803 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-316124461675239 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (-46594657269827 /
    2500000000000000 : ℚ) else
  if p = (1, 3) then (468694386362161 /
    50000000000000000 : ℚ) else
  if p = (2, 0) then (-1354127802610337 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-1932775842268401 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (4101453764996063 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-1765702369691711 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (2053217543234201 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (5862065002275439 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-10690110663805963 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (6747378935996557 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf689_polynomial_eq :
    lowerPullbackPolynomial 17 5 majorizationTriangle689 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray689 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 17 5 majorizationTriangle689
    cellMatrix_17_5 cellMatrix_17_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf689_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray689 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf689_kernel {p : ℝ × ℝ} (hp : majorizationTriangle689.Contains p) :
    (0 : ℝ) ≤ kernel (((17 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 17 5 majorizationTriangle689
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray689
    majorizationLeaf689_polynomial_eq majorizationLeaf689_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
