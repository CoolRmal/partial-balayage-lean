/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices19

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

/-- The actual closed rational triangle of majorization leaf 621. -/
def majorizationTriangle621 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 621. -/
def majorizationArray621 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (231272644838901661507587518660396326917036619399 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 1) then (-21848409932291285560404722559264955303423146083 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-789068522432347 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (2035322731691977 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-5214319192778515921822964932441011426340907041 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (1, 1) then (-110669520415457 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (-593915378429283 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (5171643249383677 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-52354311937703 /
    4687500000000000 : ℚ) else
  if p = (2, 1) then (-136274702817671 /
    10000000000000000 : ℚ) else
  if p = (2, 2) then (-1498006104561893 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (8276089180475431 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-2292386928341257 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (1921247210680517 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (10985324580345773 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-12231226480337999 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf621_polynomial_eq :
    lowerPullbackPolynomial 14 9 majorizationTriangle621 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray621 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 9 majorizationTriangle621
    cellMatrix_14_9 cellMatrix_14_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf621_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray621 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf621_kernel {p : ℝ × ℝ} (hp : majorizationTriangle621.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 9 majorizationTriangle621
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray621
    majorizationLeaf621_polynomial_eq majorizationLeaf621_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 622. -/
def majorizationTriangle622 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 622. -/
def majorizationArray622 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (214236785693936112105398946319168346505495541 /
    1426106925256758076683791106048000000000000000 : ℚ) else
  if p = (0, 1) then (77485091306331633035764978045285236945588617689 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (1649198581657829 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (-5972022353531101 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (71895796440276501490521713909220559123224232409 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (2149852408074433 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-2083668075973 /
    390625000000000 : ℚ) else
  if p = (1, 3) then (-2738631350341459 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (3951288602081273 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-1415254268965769 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-409852570448929 /
    10000000000000000 : ℚ) else
  if p = (2, 3) then (5395454593400189 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-23492358748144717 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (1090645944019033 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (539085135213209 /
    24000000000000000 : ℚ) else
  if p = (3, 3) then (-12231226480337999 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf622_polynomial_eq :
    lowerPullbackPolynomial 14 9 majorizationTriangle622 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray622 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 9 majorizationTriangle622
    cellMatrix_14_9 cellMatrix_14_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf622_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray622 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf622_kernel {p : ℝ × ℝ} (hp : majorizationTriangle622.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 9 majorizationTriangle622
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray622
    majorizationLeaf622_polynomial_eq majorizationLeaf622_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 623. -/
def majorizationTriangle623 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 623. -/
def majorizationArray623 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (214834077544882733240508601251370481908869069449 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 1) then (-89653787041984711617415960752127928639830655449 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-373650452679137 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (15860242046508089 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-59714934945964754529665598287016395759261352409 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (1910625572342889 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (3983812492525111 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-1598003487780341 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-5196593847994057 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-441429294125561 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (1056015394270329 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (-6640414896022093 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (23492358748144717 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (1090645944019033 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-539085135213209 /
    24000000000000000 : ℚ) else
  if p = (3, 3) then (8760368870262097 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf623_polynomial_eq :
    lowerPullbackPolynomial 14 10 majorizationTriangle623 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray623 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 10 majorizationTriangle623
    cellMatrix_14_10 cellMatrix_14_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf623_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray623 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf623_kernel {p : ℝ × ℝ} (hp : majorizationTriangle623.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 10 majorizationTriangle623
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray623
    majorizationLeaf623_polynomial_eq majorizationLeaf623_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 624. -/
def majorizationTriangle624 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 624. -/
def majorizationArray624 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (6204209265531991940621885624069945194091565769 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (24176458594152101951775342173577309208216671047 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (2683271435523521 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (10510317217739111 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (24176458594152101951775342173577309208216671047 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (2683271435523521 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (2683271435523521 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-3750109490421697 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (2683271435523521 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (2683271435523521 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (2683271435523521 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-10880322844502101 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-3465841614616511 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-6161581188079157 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-1347869786731323 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (8760368870262097 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf624_polynomial_eq :
    lowerPullbackPolynomial 14 10 majorizationTriangle624 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray624 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 10 majorizationTriangle624
    cellMatrix_14_10 cellMatrix_14_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf624_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray624 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf624_kernel {p : ℝ × ℝ} (hp : majorizationTriangle624.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 10 majorizationTriangle624
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray624
    majorizationLeaf624_polynomial_eq majorizationLeaf624_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 625. -/
def majorizationTriangle625 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 625. -/
def majorizationArray625 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (194753513173256253881080812225781803043908989321 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-10683396986274953703904102721183593102266795629 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (7369645344235339 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-219420508366851 /
    25000000000000000 : ℚ) else
  if p = (1, 0) then (-6730168006892267441792194123626236333268600429 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (944116559245703 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-2003102473188297 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (1266297715079797 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-1928563352081503 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (869577438138909 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-85021120291903 /
    12500000000000000 : ℚ) else
  if p = (2, 3) then (50225335121309 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (3465841614616511 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-6161581188079157 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (1347869786731323 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-23876987570011 /
    14400000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf625_polynomial_eq :
    lowerPullbackPolynomial 14 11 majorizationTriangle625 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray625 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 11 majorizationTriangle625
    cellMatrix_14_11 cellMatrix_14_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf625_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray625 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf625_kernel {p : ℝ × ℝ} (hp : majorizationTriangle625.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 11 majorizationTriangle625
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray625
    majorizationLeaf625_polynomial_eq majorizationLeaf625_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 626. -/
def majorizationTriangle626 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 626. -/
def majorizationArray626 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (32497214358872138161475135455980843945112687 /
    792281625142643375935439503360000000000000000 : ℚ) else
  if p = (0, 1) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 3) then (2683271435523521 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 3) then (2683271435523521 /
    600000000000000000 : ℚ) else
  if p = (2, 3) then (2683271435523521 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-529492956971297 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-529492956971297 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-529492956971297 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-23876987570011 /
    14400000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf626_polynomial_eq :
    lowerPullbackPolynomial 14 11 majorizationTriangle626 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray626 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 11 majorizationTriangle626
    cellMatrix_14_11 cellMatrix_14_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf626_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray626 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf626_kernel {p : ℝ × ℝ} (hp : majorizationTriangle626.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 11 majorizationTriangle626
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray626
    majorizationLeaf626_polynomial_eq majorizationLeaf626_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 627. -/
def majorizationTriangle627 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 627. -/
def majorizationArray627 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (237073948936585416423289976036550716159078959537 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-38909305640346431871502364902581964877677607659 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-529492956971297 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (529492956971297 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-38909305640346431871502364902581964877677607659 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-529492956971297 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (529492956971297 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-529492956971297 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-529492956971297 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (529492956971297 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-529492956971297 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (529492956971297 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (529492956971297 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-529492956971297 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (529492956971297 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-529492956971297 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf627_polynomial_eq :
    lowerPullbackPolynomial 14 12 majorizationTriangle627 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray627 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 12 majorizationTriangle627
    cellMatrix_14_12 cellMatrix_14_12_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf627_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray627 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf627_kernel {p : ℝ × ℝ} (hp : majorizationTriangle627.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((12 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 12 majorizationTriangle627
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray627
    majorizationLeaf627_polynomial_eq majorizationLeaf627_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 628. -/
def majorizationTriangle628 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 628. -/
def majorizationArray628 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 3) then (-529492956971297 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf628_polynomial_eq :
    lowerPullbackPolynomial 14 12 majorizationTriangle628 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray628 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 12 majorizationTriangle628
    cellMatrix_14_12 cellMatrix_14_12_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf628_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray628 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf628_kernel {p : ℝ × ℝ} (hp : majorizationTriangle628.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((12 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 12 majorizationTriangle628
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray628
    majorizationLeaf628_polynomial_eq majorizationLeaf628_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 629. -/
def majorizationTriangle629 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 629. -/
def majorizationArray629 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf629_polynomial_eq :
    lowerPullbackPolynomial 14 13 majorizationTriangle629 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray629 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 13 majorizationTriangle629
    cellMatrix_14_13 cellMatrix_14_13_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf629_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray629 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf629_kernel {p : ℝ × ℝ} (hp : majorizationTriangle629.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((13 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 13 majorizationTriangle629
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray629
    majorizationLeaf629_polynomial_eq majorizationLeaf629_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 630. -/
def majorizationTriangle630 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 630. -/
def majorizationArray630 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (47863695220208989472124366163084872295381699349 /
    356526731314189519170947776512000000000000000000 : ℚ) else
  if p = (0, 2) then (15606533007251 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (1534815446288009 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-8237763719072507 /
    62500000000000000 : ℚ) else
  if p = (1, 2) then (1512285883467 /
    10000000000000000 : ℚ) else
  if p = (1, 3) then (-140903799861089 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-181831980069869 /
    75000000000000000 : ℚ) else
  if p = (2, 2) then (-13252614438931 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (72867568438241 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (39849598631407 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (14274638691137 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-73088517790967 /
    900000000000000000 : ℚ) else
  if p = (0, 1) then (-33744736625978973 /
    250000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf630_polynomial_eq :
    lowerPullbackPolynomial 15 0 majorizationTriangle630 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray630 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 0 majorizationTriangle630
    cellMatrix_15_0 cellMatrix_15_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf630_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray630 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf630_kernel {p : ℝ × ℝ} (hp : majorizationTriangle630.Contains p) :
    (1 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 0 majorizationTriangle630
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray630
    majorizationLeaf630_polynomial_eq majorizationLeaf630_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 631. -/
def majorizationTriangle631 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 631. -/
def majorizationArray631 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (10394721003596778261901952876471756658519240569 /
    11884224377139650639031592550400000000000000000 : ℚ) else
  if p = (0, 1) then (110176267583625034886020568798426749446553475753 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (84287297356947 /
    40000000000000000 : ℚ) else
  if p = (0, 3) then (-1184529716437531 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (113695891378039351299414655499206127107436583593 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-121600429957113 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (131473064261827 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-141345698566541 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-396985197580303 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (8034718361497 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-8134418550519 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (73309467143693 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-174932026323487 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (2511862871171 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (7566150429389 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (-73088517790967 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf631_polynomial_eq :
    lowerPullbackPolynomial 15 0 majorizationTriangle631 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray631 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 0 majorizationTriangle631
    cellMatrix_15_0 cellMatrix_15_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf631_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray631 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf631_kernel {p : ℝ × ℝ} (hp : majorizationTriangle631.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 0 majorizationTriangle631
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray631
    majorizationLeaf631_polynomial_eq majorizationLeaf631_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
