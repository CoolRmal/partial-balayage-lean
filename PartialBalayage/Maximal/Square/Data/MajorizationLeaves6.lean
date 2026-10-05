/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices6

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

/-- The actual closed rational triangle of majorization leaf 384. -/
def majorizationTriangle384 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 384. -/
def majorizationArray384 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1443191124086189339897853083889809972328102058093 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 2) then (-8857112328360569 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (26104258996393151 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-89313409589689072560400833009154900485312427811 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 2) then (1663230876727027 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-278646842228033 /
    40000000000000000 : ℚ) else
  if p = (2, 0) then (-6360833697637787 /
    300000000000000000 : ℚ) else
  if p = (2, 2) then (-486110499259307 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (1153766953128797 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (277433911427081 /
    112500000000000000 : ℚ) else
  if p = (3, 2) then (245147778336601 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-65433731108839 /
    200000000000000000 : ℚ) else
  if p = (0, 1) then (-37920674973976801592254063026788683592162808417 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf384_polynomial_eq :
    lowerPullbackPolynomial 8 0 majorizationTriangle384 radialPowerData8.radius
      (certifiedRadialHeight radialPowerData8 radialPowerData32)
      (certifiedRadialSlope radialPowerData8) 1 =
        planeArrayPolynomial majorizationArray384 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 0 majorizationTriangle384
    cellMatrix_8_0 cellMatrix_8_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf384_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray384 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf384_kernel {p : ℝ × ℝ} (hp : majorizationTriangle384.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 0 majorizationTriangle384
    radialPowerData8 radialPowerData32 radialPowerData8_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray384
    majorizationLeaf384_polynomial_eq majorizationLeaf384_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 385. -/
def majorizationTriangle385 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 385. -/
def majorizationArray385 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (28410877553815728010712569143035201556650949989 /
    23768448754279301278063185100800000000000000000 : ℚ) else
  if p = (0, 1) then (73411818415698181037561521658834726105353489883 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 2) then (209211384676563 /
    20000000000000000 : ℚ) else
  if p = (0, 3) then (-8218774187769253 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (19426061505184133845436278711640669371815145289 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (1, 1) then (320889579759401 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (73594624256553 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (-615268076785613 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-763636480402439 /
    50000000000000000 : ℚ) else
  if p = (2, 1) then (199493755270789 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (41468965651917 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-282431686574623 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-5320925672873351 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (391687533366853 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (98608023306349 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-65433731108839 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf385_polynomial_eq :
    lowerPullbackPolynomial 8 0 majorizationTriangle385 radialPowerData9.radius
      (certifiedRadialHeight radialPowerData9 radialPowerData32)
      (certifiedRadialSlope radialPowerData9) 1 =
        planeArrayPolynomial majorizationArray385 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 0 majorizationTriangle385
    cellMatrix_8_0 cellMatrix_8_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf385_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray385 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf385_kernel {p : ℝ × ℝ} (hp : majorizationTriangle385.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 0 majorizationTriangle385
    radialPowerData9 radialPowerData32 radialPowerData9_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray385
    majorizationLeaf385_polynomial_eq majorizationLeaf385_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 386. -/
def majorizationTriangle386 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 386. -/
def majorizationArray386 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (846297127997842833135535657701188966072776715017 /
    570442770102703230673516442419200000000000000000 : ℚ) else
  if p = (0, 1) then (-25045203107658316058298034629344586704802000713 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (0, 2) then (8390034339672013 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (593317486706089 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-50783770403375530815906418736901044855507979739 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (1, 1) then (2473220873487613 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-853240879966441 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-40728345657323 /
    60000000000000000 : ℚ) else
  if p = (2, 0) then (-14484563437702619 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-790675043908431 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (181545954610183 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (3900219692971 /
    30000000000000000 : ℚ) else
  if p = (3, 0) then (5320925672873351 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (391687533366853 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-98608023306349 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (10646895253067 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf386_polynomial_eq :
    lowerPullbackPolynomial 8 1 majorizationTriangle386 radialPowerData9.radius
      (certifiedRadialHeight radialPowerData9 radialPowerData32)
      (certifiedRadialSlope radialPowerData9) 1 =
        planeArrayPolynomial majorizationArray386 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 1 majorizationTriangle386
    cellMatrix_8_1 cellMatrix_8_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf386_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray386 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf386_kernel {p : ℝ × ℝ} (hp : majorizationTriangle386.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 1 majorizationTriangle386
    radialPowerData9 radialPowerData32 radialPowerData9_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray386
    majorizationLeaf386_polynomial_eq majorizationLeaf386_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 387. -/
def majorizationTriangle387 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 387. -/
def majorizationArray387 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (20382625137796854106318054501047030027549933581 /
    23768448754279301278063185100800000000000000000 : ℚ) else
  if p = (0, 1) then (8704749497066962962554707483507892544755468897 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (0, 2) then (541369426339481 /
    50000000000000000 : ℚ) else
  if p = (0, 3) then (-36681929296147 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (2293589927507395893983489077630003571182360779 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (1, 1) then (-247873094831 /
    400000000000000 : ℚ) else
  if p = (1, 2) then (20468446810017 /
    5000000000000000 : ℚ) else
  if p = (1, 3) then (-2395634149461 /
    6250000000000000 : ℚ) else
  if p = (2, 0) then (-1668748053029491 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (33453365892089 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (45559028917347 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-16549697394259 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-2073819331186999 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (71921759086763 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (5154282186681 /
    40000000000000000 : ℚ) else
  if p = (3, 3) then (10646895253067 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf387_polynomial_eq :
    lowerPullbackPolynomial 8 1 majorizationTriangle387 radialPowerData10.radius
      (certifiedRadialHeight radialPowerData10 radialPowerData32)
      (certifiedRadialSlope radialPowerData10) 1 =
        planeArrayPolynomial majorizationArray387 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 1 majorizationTriangle387
    cellMatrix_8_1 cellMatrix_8_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf387_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray387 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf387_kernel {p : ℝ × ℝ} (hp : majorizationTriangle387.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 1 majorizationTriangle387
    radialPowerData10 radialPowerData32 radialPowerData10_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray387
    majorizationLeaf387_polynomial_eq majorizationLeaf387_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 388. -/
def majorizationTriangle388 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 388. -/
def majorizationArray388 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (42347421650823338062571528450340768269755136151 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 1) then (-8716900919695718083470476402260851318447147617 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (0, 2) then (3192223104361397 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-65189007018877 /
    450000000000000000 : ℚ) else
  if p = (1, 0) then (-1860369763282622520848186733778156401073412299 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (1, 1) then (359455656981501 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-1260524336539671 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-10326295616309 /
    25000000000000000 : ℚ) else
  if p = (2, 0) then (-5411315437245981 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-69915748165729 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (259550348469603 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (4442157941377 /
    18750000000000000 : ℚ) else
  if p = (3, 0) then (2073819331186999 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (71921759086763 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-5154282186681 /
    40000000000000000 : ℚ) else
  if p = (3, 3) then (-141765708943379 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf388_polynomial_eq :
    lowerPullbackPolynomial 8 2 majorizationTriangle388 radialPowerData10.radius
      (certifiedRadialHeight radialPowerData10 radialPowerData32)
      (certifiedRadialSlope radialPowerData10) 1 =
        planeArrayPolynomial majorizationArray388 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 2 majorizationTriangle388
    cellMatrix_8_2 cellMatrix_8_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf388_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray388 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf388_kernel {p : ℝ × ℝ} (hp : majorizationTriangle388.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 2 majorizationTriangle388
    radialPowerData10 radialPowerData32 radialPowerData10_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray388
    majorizationLeaf388_polynomial_eq majorizationLeaf388_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 389. -/
def majorizationTriangle389 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 389. -/
def majorizationArray389 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1791688407493313084537703379157513152195688671 /
    2971056094284912659757898137600000000000000000 : ℚ) else
  if p = (0, 1) then (208121668616106539017408938324962231400119341009 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (1925621752350943 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (239855953006981 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (173850169483561662043755684043566448695258320849 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-1866710987703527 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (924036567887347 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-105298695486667 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-657789134446211 /
    40000000000000000 : ℚ) else
  if p = (2, 1) then (-46208422590221 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (182619460850073 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-25556345379 /
    40000000000000000 : ℚ) else
  if p = (3, 0) then (-81188067724973 /
    22500000000000000 : ℚ) else
  if p = (3, 1) then (-251965304011 /
    1875000000000000 : ℚ) else
  if p = (3, 2) then (109539970871797 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-141765708943379 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf389_polynomial_eq :
    lowerPullbackPolynomial 8 2 majorizationTriangle389 radialPowerData11.radius
      (certifiedRadialHeight radialPowerData11 radialPowerData32)
      (certifiedRadialSlope radialPowerData11) 1 =
        planeArrayPolynomial majorizationArray389 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 2 majorizationTriangle389
    cellMatrix_8_2 cellMatrix_8_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf389_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray389 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf389_kernel {p : ℝ × ℝ} (hp : majorizationTriangle389.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 2 majorizationTriangle389
    radialPowerData11 radialPowerData32 radialPowerData11_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray389
    majorizationLeaf389_polynomial_eq majorizationLeaf389_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 390. -/
def majorizationTriangle390 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 390. -/
def majorizationArray390 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2184375687366352820026773865639098526300691395507 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-66007279871384006701731838981757298767504235163 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (9315913285008683 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-2606709954620969 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-44096368179618479483995083529358596465508899483 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-2409424110889257 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-1508355431331087 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (93344494106059 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-3272376486938201 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (2493368081877 /
    1600000000000000 : ℚ) else
  if p = (2, 2) then (401699402593667 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-2908178358757 /
    60000000000000000 : ℚ) else
  if p = (3, 0) then (81188067724973 /
    22500000000000000 : ℚ) else
  if p = (3, 1) then (-251965304011 /
    1875000000000000 : ℚ) else
  if p = (3, 2) then (-109539970871797 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (1570904284721 /
    150000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf390_polynomial_eq :
    lowerPullbackPolynomial 8 3 majorizationTriangle390 radialPowerData11.radius
      (certifiedRadialHeight radialPowerData11 radialPowerData32)
      (certifiedRadialSlope radialPowerData11) 1 =
        planeArrayPolynomial majorizationArray390 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 3 majorizationTriangle390
    cellMatrix_8_3 cellMatrix_8_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf390_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray390 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf390_kernel {p : ℝ × ℝ} (hp : majorizationTriangle390.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 3 majorizationTriangle390
    radialPowerData11 radialPowerData32 radialPowerData11_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray390
    majorizationLeaf390_polynomial_eq majorizationLeaf390_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 391. -/
def majorizationTriangle391 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 391. -/
def majorizationArray391 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (7359662235232653747652570439369264823146116543 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (26231836498260335780910656566852951348668929879 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (1615184777737541 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (520210059914411 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (73784845601703248523868082766264224373729019397 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-3380718862812473 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (589971307221599 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (83516315166437 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-8636083227460549 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-586050102480333 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (34477705735831 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (5115466085459 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-112295395046663 /
    36000000000000000 : ℚ) else
  if p = (3, 1) then (-20830747056419 /
    25000000000000000 : ℚ) else
  if p = (3, 2) then (100114545163471 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (1570904284721 /
    150000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf391_polynomial_eq :
    lowerPullbackPolynomial 8 3 majorizationTriangle391 radialPowerData12.radius
      (certifiedRadialHeight radialPowerData12 radialPowerData32)
      (certifiedRadialSlope radialPowerData12) 1 =
        planeArrayPolynomial majorizationArray391 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 3 majorizationTriangle391
    cellMatrix_8_3 cellMatrix_8_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf391_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray391 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf391_kernel {p : ℝ × ℝ} (hp : majorizationTriangle391.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 3 majorizationTriangle391
    radialPowerData12 radialPowerData32 radialPowerData12_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray391
    majorizationLeaf391_polynomial_eq majorizationLeaf391_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 392. -/
def majorizationTriangle392 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 392. -/
def majorizationArray392 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (785152406556583074693258569997396746323953163711 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-22957007790826389684981531862913742856967558999 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (820498675153349 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (-4877842392635717 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-55651946588883846284853293109311308595358746117 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-1010551399425439 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-1134977454906851 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (137070048624299 /
    50000000000000000 : ℚ) else
  if p = (2, 0) then (-14250852979793699 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (1085988031834389 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (372617619006097 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-72659823945869 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (112295395046663 /
    36000000000000000 : ℚ) else
  if p = (3, 1) then (-20830747056419 /
    25000000000000000 : ℚ) else
  if p = (3, 2) then (-100114545163471 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (9025871386889 /
    50000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf392_polynomial_eq :
    lowerPullbackPolynomial 8 4 majorizationTriangle392 radialPowerData12.radius
      (certifiedRadialHeight radialPowerData12 radialPowerData32)
      (certifiedRadialSlope radialPowerData12) 1 =
        planeArrayPolynomial majorizationArray392 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 4 majorizationTriangle392
    cellMatrix_8_4 cellMatrix_8_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf392_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray392 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf392_kernel {p : ℝ × ℝ} (hp : majorizationTriangle392.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 4 majorizationTriangle392
    radialPowerData12 radialPowerData32 radialPowerData12_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray392
    majorizationLeaf392_polynomial_eq majorizationLeaf392_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 393. -/
def majorizationTriangle393 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 393. -/
def majorizationArray393 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (18767412398555928745585140448897408487377473941 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (1371619314490277600393574778378875195119731437 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (0, 2) then (-4624882661831981 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (3120033719784761 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (4208794251510831129645699660402240764148222151 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (-3753446706969983 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-217243463064089 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (100901846285711 /
    75000000000000000 : ℚ) else
  if p = (2, 0) then (-6617114555621033 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-134895987639939 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (-83958692959793 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (64086805409737 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (-47990000790227 /
    22500000000000000 : ℚ) else
  if p = (3, 1) then (-8991636563749 /
    9375000000000000 : ℚ) else
  if p = (3, 2) then (-62351139800531 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (9025871386889 /
    50000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf393_polynomial_eq :
    lowerPullbackPolynomial 8 4 majorizationTriangle393 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray393 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 4 majorizationTriangle393
    cellMatrix_8_4 cellMatrix_8_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf393_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray393 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf393_kernel {p : ℝ × ℝ} (hp : majorizationTriangle393.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 4 majorizationTriangle393
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray393
    majorizationLeaf393_polynomial_eq majorizationLeaf393_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 394. -/
def majorizationTriangle394 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 394. -/
def majorizationArray394 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (46550065796388069061393797284004252217938384319 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 1) then (-3428581387544260524173378975770911809590823111 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (0, 2) then (-1884397136501563 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-221245573775143 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (-3363358988192133134059019626182743351303637191 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (-5677871323449309 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (509863128584737 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (15044792458813 /
    60000000000000000 : ℚ) else
  if p = (2, 0) then (-3485438206279731 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (1249944678279631 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-41732194512171 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (-1365345630911 /
    10000000000000000 : ℚ) else
  if p = (3, 0) then (47990000790227 /
    22500000000000000 : ℚ) else
  if p = (3, 1) then (-8991636563749 /
    9375000000000000 : ℚ) else
  if p = (3, 2) then (62351139800531 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (18031486338337 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf394_polynomial_eq :
    lowerPullbackPolynomial 8 5 majorizationTriangle394 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray394 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 5 majorizationTriangle394
    cellMatrix_8_5 cellMatrix_8_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf394_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray394 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf394_kernel {p : ℝ × ℝ} (hp : majorizationTriangle394.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 5 majorizationTriangle394
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray394
    majorizationLeaf394_polynomial_eq majorizationLeaf394_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 395. -/
def majorizationTriangle395 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 395. -/
def majorizationArray395 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (9240957478499184196886912367317842025714871049 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (8255869378041634826955307762003985732783071827 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (0, 2) then (-1432185764486023 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (1103860396112111 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (5089627668837406087820106658695859283627254117 /
    38029518006846882044901096161280000000000000000 : ℚ) else
  if p = (1, 1) then (-1657160922812329 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-55470349570309 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (4637935217147 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-98188801428353 /
    12000000000000000 : ℚ) else
  if p = (2, 1) then (-221336650381893 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-36961986119029 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (63889251516323 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-20039553344959 /
    14400000000000000 : ℚ) else
  if p = (3, 1) then (-12321147781579 /
    24000000000000000 : ℚ) else
  if p = (3, 2) then (-142733765939399 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (18031486338337 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf395_polynomial_eq :
    lowerPullbackPolynomial 8 5 majorizationTriangle395 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray395 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 5 majorizationTriangle395
    cellMatrix_8_5 cellMatrix_8_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf395_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray395 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf395_kernel {p : ℝ × ℝ} (hp : majorizationTriangle395.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 5 majorizationTriangle395
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray395
    majorizationLeaf395_polynomial_eq majorizationLeaf395_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
