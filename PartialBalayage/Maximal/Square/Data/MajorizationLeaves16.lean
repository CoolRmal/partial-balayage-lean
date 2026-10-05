/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices16

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

/-- The actual closed rational triangle of majorization leaf 584. -/
def majorizationTriangle584 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 584. -/
def majorizationArray584 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2228948717366942059881449803559350976432315350189 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-81534958342463018101370723674816020656637424423 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-2860915543538059 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-44492080193143 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-82268263221329855170453785179848181817430061863 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-728769450868121 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (118894102311409 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (57413140850011 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-2221402659444139 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (29980986668887 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-23310106807603 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-19689649498073 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (76749967059283 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-2513399944863 /
    20000000000000000 : ℚ) else
  if p = (3, 2) then (-12632385242213 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (4423363722143 /
    75000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf584_polynomial_eq :
    lowerPullbackPolynomial 13 5 majorizationTriangle584 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray584 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 5 majorizationTriangle584
    cellMatrix_13_5 cellMatrix_13_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf584_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray584 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf584_kernel {p : ℝ × ℝ} (hp : majorizationTriangle584.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 5 majorizationTriangle584
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray584
    majorizationLeaf584_polynomial_eq majorizationLeaf584_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 585. -/
def majorizationTriangle585 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 585. -/
def majorizationArray585 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (42963173487499806079293211359579826337348141339 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (3512721574199627256335538607696955237526916619 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 2) then (-1449331871425273 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (99745138446493 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (10365524865692204344627177542662534013632080417 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (-302377633129839 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-46222545702391 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (9087194638601 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-17990614151527 /
    4687500000000000 : ℚ) else
  if p = (2, 1) then (11934873177981 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (-46346764213 /
    6250000000000000 : ℚ) else
  if p = (2, 3) then (-15697260279071 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (846792860819 /
    36000000000000000 : ℚ) else
  if p = (3, 1) then (-1977080998331 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (-40447979423503 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (4423363722143 /
    75000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf585_polynomial_eq :
    lowerPullbackPolynomial 13 5 majorizationTriangle585 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray585 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 5 majorizationTriangle585
    cellMatrix_13_5 cellMatrix_13_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf585_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray585 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf585_kernel {p : ℝ × ℝ} (hp : majorizationTriangle585.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 5 majorizationTriangle585
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray585
    majorizationLeaf585_polynomial_eq majorizationLeaf585_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 586. -/
def majorizationTriangle586 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 586. -/
def majorizationArray586 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (122276239747607646737822337496344282733386023413 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-10231631030662481478862165643396840077838477857 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (-1630672132638173 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-18791938575957 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-9461678582885007981255485632685831502067362337 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (-108392026348823 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (8815362158071 /
    10000000000000000 : ℚ) else
  if p = (1, 3) then (113058751754701 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1130229484177253 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-37854087720269 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-41189527650911 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (3376376993939 /
    40000000000000000 : ℚ) else
  if p = (3, 0) then (-846792860819 /
    36000000000000000 : ℚ) else
  if p = (3, 1) then (-1977080998331 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (40447979423503 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-321463586954381 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf586_polynomial_eq :
    lowerPullbackPolynomial 13 6 majorizationTriangle586 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray586 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 6 majorizationTriangle586
    cellMatrix_13_6 cellMatrix_13_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf586_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray586 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf586_kernel {p : ℝ × ℝ} (hp : majorizationTriangle586.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 6 majorizationTriangle586
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray586
    majorizationLeaf586_polynomial_eq majorizationLeaf586_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 587. -/
def majorizationTriangle587 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 587. -/
def majorizationArray587 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2287712291011049908321561321191759496594139803 /
    4456584141427368989636847206400000000000000000 : ℚ) else
  if p = (0, 1) then (1781175623072760837134863590965185204103088737 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (0, 2) then (-1449070778498591 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-130546463341 /
    450000000000000000 : ℚ) else
  if p = (1, 0) then (4845937386777271403899111685425853503821913891 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 1) then (-65872326103953 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (1833554247091 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (-10711352538151 /
    60000000000000000 : ℚ) else
  if p = (2, 0) then (-358062848634593 /
    75000000000000000 : ℚ) else
  if p = (2, 1) then (46157888797347 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (-17018814281257 /
    12500000000000000 : ℚ) else
  if p = (2, 3) then (16926120752831 /
    37500000000000000 : ℚ) else
  if p = (3, 0) then (60142594468081 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-59814159747893 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (641513674953 /
    1600000000000000 : ℚ) else
  if p = (3, 3) then (-321463586954381 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf587_polynomial_eq :
    lowerPullbackPolynomial 13 6 majorizationTriangle587 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray587 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 6 majorizationTriangle587
    cellMatrix_13_6 cellMatrix_13_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf587_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray587 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf587_kernel {p : ℝ × ℝ} (hp : majorizationTriangle587.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 6 majorizationTriangle587
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray587
    majorizationLeaf587_polynomial_eq majorizationLeaf587_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 588. -/
def majorizationTriangle588 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 588. -/
def majorizationArray588 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (105213112656097601357229042603106100750378730913 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-1759632529183259984572868471068404365075090017 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (0, 2) then (-3430471712459959 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-60006303940391 /
    180000000000000000 : ℚ) else
  if p = (1, 0) then (-1432144285906827294449430001717933136335014497 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (1, 1) then (32105132682249 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (289365994916121 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (19126521590913 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-2684075005672501 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-189820631135097 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-31733400392737 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-203186025860929 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-60142594468081 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-59814159747893 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-641513674953 /
    1600000000000000 : ℚ) else
  if p = (3, 3) then (1134714226046597 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf588_polynomial_eq :
    lowerPullbackPolynomial 13 7 majorizationTriangle588 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray588 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 7 majorizationTriangle588
    cellMatrix_13_7 cellMatrix_13_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf588_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray588 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf588_kernel {p : ℝ × ℝ} (hp : majorizationTriangle588.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 7 majorizationTriangle588
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray588
    majorizationLeaf588_polynomial_eq majorizationLeaf588_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 589. -/
def majorizationTriangle589 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 589. -/
def majorizationArray589 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (7524256708357944454771262581892578795669796491 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (88356696984999019907731795843114123048065460303 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-647665827376727 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (113395859962151 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (72554436190667227901563414720516211636488136783 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-119586224636721 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-422060818171631 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (436729252148359 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-4060853031388669 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (185522993054261 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (456041145824627 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-242780724774913 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (38217984926351 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (59267061323521 /
    75000000000000000 : ℚ) else
  if p = (3, 2) then (-447073298969611 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (1134714226046597 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf589_polynomial_eq :
    lowerPullbackPolynomial 13 7 majorizationTriangle589 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray589 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 7 majorizationTriangle589
    cellMatrix_13_7 cellMatrix_13_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf589_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray589 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf589_kernel {p : ℝ × ℝ} (hp : majorizationTriangle589.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 7 majorizationTriangle589
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray589
    majorizationLeaf589_polynomial_eq majorizationLeaf589_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 590. -/
def majorizationTriangle590 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 590. -/
def majorizationArray590 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (155858312998838061372340817804896644669283990181 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-89421439183835282942388258923044423128767555663 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-1343511583954623 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-1276779090452531 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-20056516583095024239834217917286951828131685061 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (725596252059969 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (404125124461599 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (375521310906253 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-1251703050659287 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-659659483642429 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-87621090422919 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (715597847199457 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-38217984926351 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (59267061323521 /
    75000000000000000 : ℚ) else
  if p = (3, 2) then (447073298969611 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-416765120214787 /
    180000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf590_polynomial_eq :
    lowerPullbackPolynomial 13 8 majorizationTriangle590 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray590 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 8 majorizationTriangle590
    cellMatrix_13_8 cellMatrix_13_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf590_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray590 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf590_kernel {p : ℝ × ℝ} (hp : majorizationTriangle590.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 8 majorizationTriangle590
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray590
    majorizationLeaf590_polynomial_eq majorizationLeaf590_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 591. -/
def majorizationTriangle591 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 591. -/
def majorizationArray591 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1165822730418857629473208834072632710474889959 /
    3565267313141895191709477765120000000000000000 : ℚ) else
  if p = (0, 1) then (92555863599163080138470267533706848785806745821 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-789068522432347 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-9117227461583 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (22578018061113376319575652161979721562735015327 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-110669520415457 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (593915378429283 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-1609891575030197 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-52354311937703 /
    4687500000000000 : ℚ) else
  if p = (2, 1) then (136274702817671 /
    10000000000000000 : ℚ) else
  if p = (2, 2) then (-1498006104561893 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (1150684451649471 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (92136453994127 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (-952610757840629 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (409188075526081 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (-416765120214787 /
    180000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf591_polynomial_eq :
    lowerPullbackPolynomial 13 8 majorizationTriangle591 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray591 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 8 majorizationTriangle591
    cellMatrix_13_8 cellMatrix_13_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf591_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray591 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf591_kernel {p : ℝ × ℝ} (hp : majorizationTriangle591.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 8 majorizationTriangle591
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray591
    majorizationLeaf591_polynomial_eq majorizationLeaf591_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 592. -/
def majorizationTriangle592 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 592. -/
def majorizationArray592 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1104588183064013990485099920800622374009609401463 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-32761454748006270666436167200411699788598244767 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-13268284605791 /
    1500000000000000 : ℚ) else
  if p = (0, 3) then (71107179896989 /
    72000000000000000 : ℚ) else
  if p = (1, 0) then (-15693535451542018401752375366778762043185984927 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (1330205216850963 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (765344528590179 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-1809554084024671 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1583201528012369 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-410136270336081 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (138746197542431 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-1294891847067083 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-92136453994127 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (-952610757840629 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-409188075526081 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (1595163504590419 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf592_polynomial_eq :
    lowerPullbackPolynomial 13 9 majorizationTriangle592 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray592 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 9 majorizationTriangle592
    cellMatrix_13_9 cellMatrix_13_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf592_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray592 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf592_kernel {p : ℝ × ℝ} (hp : majorizationTriangle592.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 9 majorizationTriangle592
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray592
    majorizationLeaf592_polynomial_eq majorizationLeaf592_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 593. -/
def majorizationTriangle593 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 593. -/
def majorizationArray593 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5426090083166517378600664044771826235806011233 /
    23768448754279301278063185100800000000000000000 : ℚ) else
  if p = (0, 1) then (23542793496720360565542124094727131842251618403 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-373650452679137 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-2035322731691977 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (16058080472715371293604533478449248622109292643 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (1910625572342889 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-3983812492525111 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (5171643249383677 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-5196593847994057 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (441429294125561 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (1056015394270329 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (-8276089180475431 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (197929473378241 /
    56250000000000000 : ℚ) else
  if p = (3, 1) then (27968757586099 /
    15000000000000000 : ℚ) else
  if p = (3, 2) then (-3148738211666933 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (1595163504590419 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf593_polynomial_eq :
    lowerPullbackPolynomial 13 9 majorizationTriangle593 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray593 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 9 majorizationTriangle593
    cellMatrix_13_9 cellMatrix_13_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf593_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray593 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf593_kernel {p : ℝ × ℝ} (hp : majorizationTriangle593.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 9 majorizationTriangle593
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray593
    majorizationLeaf593_polynomial_eq majorizationLeaf593_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 594. -/
def majorizationTriangle594 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 594. -/
def majorizationArray594 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (194938751884522007076600007241401451024632559239 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 1) then (-8927070309678831174623393203501189146636986401 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (0, 2) then (-141185373795667 /
    24000000000000000 : ℚ) else
  if p = (0, 3) then (5930392469238929 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-6215637172738234371589769099478517224700934243 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (3912234464037971 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-278865026844313 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (2469561540190873 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-9256038395878459 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-1560179597569521 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-1017399451982221 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-2919429054484077 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-197929473378241 /
    56250000000000000 : ℚ) else
  if p = (3, 1) then (27968757586099 /
    15000000000000000 : ℚ) else
  if p = (3, 2) then (3148738211666933 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (1058936133715069 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf594_polynomial_eq :
    lowerPullbackPolynomial 13 10 majorizationTriangle594 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray594 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 10 majorizationTriangle594
    cellMatrix_13_10 cellMatrix_13_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf594_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray594 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf594_kernel {p : ℝ × ℝ} (hp : majorizationTriangle594.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 10 majorizationTriangle594
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray594
    majorizationLeaf594_polynomial_eq majorizationLeaf594_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 595. -/
def majorizationTriangle595 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 595. -/
def majorizationArray595 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (4941797165178873649508561572072826170737992429 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (22691555669688472786107820919372926069208700403 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (7369645344235339 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-15860242046508089 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (14785097710923100261884003724258212531212310003 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (944116559245703 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (2003102473188297 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-1598003487780341 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-1928563352081503 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-869577438138909 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-85021120291903 /
    12500000000000000 : ℚ) else
  if p = (2, 3) then (6640414896022093 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-46960440884531 /
    4687500000000000 : ℚ) else
  if p = (3, 1) then (1583157541754183 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (-701279057563667 /
    50000000000000000 : ℚ) else
  if p = (3, 3) then (1058936133715069 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf595_polynomial_eq :
    lowerPullbackPolynomial 13 10 majorizationTriangle595 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray595 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 13 10 majorizationTriangle595
    cellMatrix_13_10 cellMatrix_13_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf595_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray595 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf595_kernel {p : ℝ × ℝ} (hp : majorizationTriangle595.Contains p) :
    (0 : ℝ) ≤ kernel (((13 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 13 10 majorizationTriangle595
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray595
    majorizationLeaf595_polynomial_eq majorizationLeaf595_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
