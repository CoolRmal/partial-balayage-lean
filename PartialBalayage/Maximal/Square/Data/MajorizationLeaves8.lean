/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices8

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

/-- The actual closed rational triangle of majorization leaf 429. -/
def majorizationTriangle429 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 429. -/
def majorizationArray429 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (277331924646088775968946372005878461587229324437 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 1) then (-84552094909480455192729401108214178480517432837 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (1925621752350943 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-520210059914411 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (-67416345343208016705902773967516287128086922757 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-1866710987703527 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-924036567887347 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (83516315166437 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-657789134446211 /
    40000000000000000 : ℚ) else
  if p = (2, 1) then (46208422590221 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (182619460850073 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-5115466085459 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (4212066678181363 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-856354656903 /
    40000000000000000 : ℚ) else
  if p = (3, 2) then (-22304451392117 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-556136218061 /
    14400000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf429_polynomial_eq :
    lowerPullbackPolynomial 9 3 majorizationTriangle429 radialPowerData12.radius
      (certifiedRadialHeight radialPowerData12 radialPowerData32)
      (certifiedRadialSlope radialPowerData12) 1 =
        planeArrayPolynomial majorizationArray429 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 3 majorizationTriangle429
    cellMatrix_9_3 cellMatrix_9_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf429_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray429 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf429_kernel {p : ℝ × ℝ} (hp : majorizationTriangle429.Contains p) :
    (1 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 3 majorizationTriangle429
    radialPowerData12 radialPowerData32 radialPowerData12_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray429
    majorizationLeaf429_polynomial_eq majorizationLeaf429_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 430. -/
def majorizationTriangle430 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 430. -/
def majorizationArray430 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (18692848850679526963238057875970678272132256149 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (4387268117153881460059043153610101904328394951 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (0, 2) then (270614963460467 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (3259694521088423 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (4314277160267859464724021908535210237949151431 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (-2335589907747211 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (337015728513031 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (244086369066287 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-4598982890273797 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-459078852584929 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (80567050029413 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (79747959428543 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-21026564256181 /
    9375000000000000 : ℚ) else
  if p = (3, 1) then (-31742812473851 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (15303579774957 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-556136218061 /
    14400000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf430_polynomial_eq :
    lowerPullbackPolynomial 9 3 majorizationTriangle430 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray430 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 3 majorizationTriangle430
    cellMatrix_9_3 cellMatrix_9_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf430_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray430 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf430_kernel {p : ℝ × ℝ} (hp : majorizationTriangle430.Contains p) :
    (1 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 3 majorizationTriangle430
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray430
    majorizationLeaf430_polynomial_eq majorizationLeaf430_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 431. -/
def majorizationTriangle431 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 431. -/
def majorizationArray431 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (141703172843877388766285369159287998478362132797 /
    356526731314189519170947776512000000000000000000 : ℚ) else
  if p = (0, 1) then (-1321941640931970974489450194331042991016870637 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (0, 2) then (1615184777737541 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-3120033719784761 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-3658908429478552997289357649599714618533251271 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (-3380718862812473 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-589971307221599 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (100901846285711 /
    75000000000000000 : ℚ) else
  if p = (2, 0) then (-8636083227460549 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (586050102480333 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (34477705735831 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (-64086805409737 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (21026564256181 /
    9375000000000000 : ℚ) else
  if p = (3, 1) then (-31742812473851 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (-15303579774957 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (164320408907851 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf431_polynomial_eq :
    lowerPullbackPolynomial 9 4 majorizationTriangle431 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray431 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 4 majorizationTriangle431
    cellMatrix_9_4 cellMatrix_9_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf431_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray431 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf431_kernel {p : ℝ × ℝ} (hp : majorizationTriangle431.Contains p) :
    (1 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 4 majorizationTriangle431
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray431
    majorizationLeaf431_polynomial_eq majorizationLeaf431_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 432. -/
def majorizationTriangle432 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 432. -/
def majorizationArray432 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (8962911050310495286745351572863211639392496393 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (24460066079259639513508724986588912456912152313 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 2) then (-519066177657623 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (1474381461573817 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (25158231327733558674148395746795332771834570489 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (1, 1) then (-255078062885763 /
    20000000000000000 : ℚ) else
  if p = (1, 2) then (-30456251850653 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (152946911971881 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-768017998790467 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-264093069956329 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-2864940675421 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (30675604243699 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-709008512091833 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-146293798287037 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-72498930258109 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (164320408907851 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf432_polynomial_eq :
    lowerPullbackPolynomial 9 4 majorizationTriangle432 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray432 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 4 majorizationTriangle432
    cellMatrix_9_4 cellMatrix_9_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf432_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray432 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf432_kernel {p : ℝ × ℝ} (hp : majorizationTriangle432.Contains p) :
    (1 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 4 majorizationTriangle432
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray432
    majorizationLeaf432_polynomial_eq majorizationLeaf432_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 433. -/
def majorizationTriangle433 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 433. -/
def majorizationArray433 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5725351124873040448756349356608107569940148523 /
    22817710804108129226940657696768000000000000000 : ℚ) else
  if p = (0, 1) then (-7162137723190587109835377255570782098445591123 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (0, 2) then (-4624882661831981 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-1103860396112111 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-4417521108205550126336394769682456687917310309 /
    38029518006846882044901096161280000000000000000 : ℚ) else
  if p = (1, 1) then (-3753446706969983 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (217243463064089 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (4637935217147 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-6617114555621033 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (134895987639939 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (-83958692959793 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-63889251516323 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (709008512091833 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-146293798287037 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (72498930258109 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (15821823134111 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf433_polynomial_eq :
    lowerPullbackPolynomial 9 5 majorizationTriangle433 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray433 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 5 majorizationTriangle433
    cellMatrix_9_5 cellMatrix_9_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf433_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray433 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf433_kernel {p : ℝ × ℝ} (hp : majorizationTriangle433.Contains p) :
    (1 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 5 majorizationTriangle433
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray433
    majorizationLeaf433_polynomial_eq majorizationLeaf433_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 434. -/
def majorizationTriangle434 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 434. -/
def majorizationArray434 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (248683195825356553920431811779108910427317 /
    1584563250285286751870879006720000000000000000 : ℚ) else
  if p = (0, 1) then (185678197252558943 /
    1500000000000000000 : ℚ) else
  if p = (0, 2) then (-220489473252651 /
    25000000000000000 : ℚ) else
  if p = (0, 3) then (14240224210033 /
    22500000000000000 : ℚ) else
  if p = (1, 0) then (61914695187743731 /
    500000000000000000 : ℚ) else
  if p = (1, 1) then (-1143937386830453 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-2204388246783 /
    3125000000000000 : ℚ) else
  if p = (1, 3) then (38511680783 /
    1200000000000000 : ℚ) else
  if p = (2, 0) then (-48112856894609 /
    20000000000000000 : ℚ) else
  if p = (2, 1) then (-291886885599983 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (523807765539 /
    1562500000000000 : ℚ) else
  if p = (2, 3) then (-19626789172669 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (-173302718228969 /
    90000000000000000 : ℚ) else
  if p = (3, 1) then (7055023521809 /
    30000000000000000 : ℚ) else
  if p = (3, 2) then (-53723834616277 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (15821823134111 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf434_polynomial_eq :
    lowerPullbackPolynomial 9 5 majorizationTriangle434 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray434 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 5 majorizationTriangle434
    cellMatrix_9_5 cellMatrix_9_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf434_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray434 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf434_kernel {p : ℝ × ℝ} (hp : majorizationTriangle434.Contains p) :
    (1 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 5 majorizationTriangle434
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray434
    majorizationLeaf434_polynomial_eq majorizationLeaf434_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 435. -/
def majorizationTriangle435 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 435. -/
def majorizationArray435 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (42660242733920467690035005271937790137774869269 /
    356526731314189519170947776512000000000000000000 : ℚ) else
  if p = (0, 1) then (-54831194780730951 /
    500000000000000000 : ℚ) else
  if p = (0, 2) then (-1432185764486023 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (12357508557293 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-169862021117591393 /
    1500000000000000000 : ℚ) else
  if p = (1, 1) then (-1657160922812329 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (55470349570309 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (-77739233676053 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-98188801428353 /
    12000000000000000 : ℚ) else
  if p = (2, 1) then (221336650381893 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-36961986119029 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-22548716356171 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (173302718228969 /
    90000000000000000 : ℚ) else
  if p = (3, 1) then (7055023521809 /
    30000000000000000 : ℚ) else
  if p = (3, 2) then (53723834616277 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (143116397478727 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf435_polynomial_eq :
    lowerPullbackPolynomial 9 6 majorizationTriangle435 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray435 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 6 majorizationTriangle435
    cellMatrix_9_6 cellMatrix_9_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf435_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray435 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf435_kernel {p : ℝ × ℝ} (hp : majorizationTriangle435.Contains p) :
    (1 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 6 majorizationTriangle435
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray435
    majorizationLeaf435_polynomial_eq majorizationLeaf435_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 436. -/
def majorizationTriangle436 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 436. -/
def majorizationArray436 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (31226387772422353583840654825335435800587062891 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (119578903566309942050785599330939563665036286633 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-3007074992601517 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (72240262713941 /
    180000000000000000 : ℚ) else
  if p = (1, 0) then (112268098503631784265688751447062829289256917673 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-111555333987957 /
    10000000000000000 : ℚ) else
  if p = (1, 2) then (42156376946173 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-112696800843229 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (292274018569409 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-198334701897041 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (71258821199603 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-37735124205107 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-4677158188761971 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (714007544845123 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-71602347188767 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (143116397478727 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf436_polynomial_eq :
    lowerPullbackPolynomial 9 6 majorizationTriangle436 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray436 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 6 majorizationTriangle436
    cellMatrix_9_6 cellMatrix_9_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf436_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray436 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf436_kernel {p : ℝ × ℝ} (hp : majorizationTriangle436.Contains p) :
    (0 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 6 majorizationTriangle436
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray436
    majorizationLeaf436_polynomial_eq majorizationLeaf436_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 437. -/
def majorizationTriangle437 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 437. -/
def majorizationArray437 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2830282824336030235878693698082867483815530910059 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-106333018167072811388773965305242911933942864553 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-5691670532272213 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-494184268275479 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-106709352197301810677997477824743063699457186473 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-620755350018069 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-11336302746923 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-385711490662337 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-4092610151623153 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (79331262743041 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-215494093544629 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-38970252745611 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (4677158188761971 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (714007544845123 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (71602347188767 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (87017699169827 /
    150000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf437_polynomial_eq :
    lowerPullbackPolynomial 9 7 majorizationTriangle437 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray437 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 7 majorizationTriangle437
    cellMatrix_9_7 cellMatrix_9_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf437_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray437 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf437_kernel {p : ℝ × ℝ} (hp : majorizationTriangle437.Contains p) :
    (0 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 7 majorizationTriangle437
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray437
    majorizationLeaf437_polynomial_eq majorizationLeaf437_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 438. -/
def majorizationTriangle438 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 438. -/
def majorizationArray438 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (53113655921752322236300327887848699603844885131 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (66059516231964965816637026281998335262458794889 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-10274626090663079 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (94677246788001 /
    40000000000000000 : ℚ) else
  if p = (1, 0) then (55276927116661035255375627180742226599137399689 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-549295157193317 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (431056352315099 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-115581199474251 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (4319419018902019 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-2005675724187667 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (1069819274200297 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-309100543933697 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-8937428421166769 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (2474243406770717 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-1402224125981759 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (87017699169827 /
    150000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf438_polynomial_eq :
    lowerPullbackPolynomial 9 7 majorizationTriangle438 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray438 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 7 majorizationTriangle438
    cellMatrix_9_7 cellMatrix_9_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf438_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray438 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf438_kernel {p : ℝ × ℝ} (hp : majorizationTriangle438.Contains p) :
    (0 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 7 majorizationTriangle438
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray438
    majorizationLeaf438_polynomial_eq majorizationLeaf438_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 439. -/
def majorizationTriangle439 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 439. -/
def majorizationArray439 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1231289528430814694910747650226542209886797909367 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-56724686855112506787486130656377561770713043849 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-143484466741973 /
    12000000000000000 : ℚ) else
  if p = (0, 3) then (-43939931383783 /
    15000000000000000 : ℚ) else
  if p = (1, 0) then (-55040359442478445833953035141764196505764123529 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-2141791913785601 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-584235387366967 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-1347748677301591 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-18472037609059 /
    2400000000000000 : ℚ) else
  if p = (2, 1) then (-9371353651661 /
    4000000000000000 : ℚ) else
  if p = (2, 2) then (-166202425890731 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-452174008149527 /
    50000000000000000 : ℚ) else
  if p = (3, 0) then (8937428421166769 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (2474243406770717 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (1402224125981759 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (4681842620458301 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf439_polynomial_eq :
    lowerPullbackPolynomial 9 8 majorizationTriangle439 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray439 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 8 majorizationTriangle439
    cellMatrix_9_8 cellMatrix_9_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf439_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray439 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf439_kernel {p : ℝ × ℝ} (hp : majorizationTriangle439.Contains p) :
    (0 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 8 majorizationTriangle439
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray439
    majorizationLeaf439_polynomial_eq majorizationLeaf439_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 440. -/
def majorizationTriangle440 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 440. -/
def majorizationArray440 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (8294832858223002408209345796108289299884660863 /
    14261069252567580766837911060480000000000000000 : ℚ) else
  if p = (0, 1) then (63698094567537609113713569299118536018884759821 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-169765692081721 /
    3000000000000000 : ℚ) else
  if p = (0, 3) then (2630945813964569 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (39344907184847544647885413959485972473580818701 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-1451557883504223 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (328587424466901 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (-2197643043420109 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (2216534377764649 /
    60000000000000000 : ℚ) else
  if p = (2, 1) then (-319118850904221 /
    5000000000000000 : ℚ) else
  if p = (2, 2) then (2422314759445219 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-2873146587860193 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-346123588807991 /
    18000000000000000 : ℚ) else
  if p = (3, 1) then (3220703253351523 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (-7723875993678331 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (4681842620458301 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf440_polynomial_eq :
    lowerPullbackPolynomial 9 8 majorizationTriangle440 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray440 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 8 majorizationTriangle440
    cellMatrix_9_8 cellMatrix_9_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf440_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray440 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf440_kernel {p : ℝ × ℝ} (hp : majorizationTriangle440.Contains p) :
    (0 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 8 majorizationTriangle440
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray440
    majorizationLeaf440_polynomial_eq majorizationLeaf440_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
