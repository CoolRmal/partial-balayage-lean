/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices5

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

/-- The actual closed rational triangle of majorization leaf 347. -/
def majorizationTriangle347 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 347. -/
def majorizationArray347 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (84253613800339611255653400354020089166715835137 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (0, 1) then (-2811812611469652715683593341306164083740437523 /
    7605903601369376408980219232256000000000000000 : ℚ) else
  if p = (0, 2) then (4756397721142893 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (369993694479881 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-11812949662502525537254843238955992287964802889 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (1, 1) then (1624938658128051 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-1911924828795543 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-146585173561651 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-9244477186313103 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-183180852063581 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (391850143786269 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (4572609585237 /
    8000000000000000 : ℚ) else
  if p = (3, 0) then (638860291511187 /
    100000000000000000 : ℚ) else
  if p = (3, 1) then (28316275974463 /
    30000000000000000 : ℚ) else
  if p = (3, 2) then (-22049965886111 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-200796664768711 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf347_polynomial_eq :
    lowerPullbackPolynomial 7 2 majorizationTriangle347 radialPowerData9.radius
      (certifiedRadialHeight radialPowerData9 radialPowerData32)
      (certifiedRadialSlope radialPowerData9) 1 =
        planeArrayPolynomial majorizationArray347 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 2 majorizationTriangle347
    cellMatrix_7_2 cellMatrix_7_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf347_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray347 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf347_kernel {p : ℝ × ℝ} (hp : majorizationTriangle347.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 2 majorizationTriangle347
    radialPowerData9 radialPowerData32 radialPowerData9_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray347
    majorizationLeaf347_polynomial_eq majorizationLeaf347_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 348. -/
def majorizationTriangle348 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 348. -/
def majorizationArray348 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (56432580022751418658494477077338168697117212711 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (2593795180649434238749088921721168636613318859 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (0, 2) then (9315913285008683 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (65189007018877 /
    450000000000000000 : ℚ) else
  if p = (1, 0) then (1909079190281761513194815313833709189675964619 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (1, 1) then (-2409424110889257 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (1508355431331087 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-10326295616309 /
    25000000000000000 : ℚ) else
  if p = (2, 0) then (-3272376486938201 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (-2493368081877 /
    1600000000000000 : ℚ) else
  if p = (2, 2) then (401699402593667 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-4442157941377 /
    18750000000000000 : ℚ) else
  if p = (3, 0) then (-12600765754950437 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (100929264087217 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (333096460085377 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-200796664768711 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf348_polynomial_eq :
    lowerPullbackPolynomial 7 2 majorizationTriangle348 radialPowerData10.radius
      (certifiedRadialHeight radialPowerData10 radialPowerData32)
      (certifiedRadialSlope radialPowerData10) 1 =
        planeArrayPolynomial majorizationArray348 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 2 majorizationTriangle348
    cellMatrix_7_2 cellMatrix_7_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf348_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray348 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf348_kernel {p : ℝ × ℝ} (hp : majorizationTriangle348.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 2 majorizationTriangle348
    radialPowerData10 radialPowerData32 radialPowerData10_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray348
    majorizationLeaf348_polynomial_eq majorizationLeaf348_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 349. -/
def majorizationTriangle349 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 349. -/
def majorizationArray349 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (112890499355664879283182196645449523412517530053 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 1) then (-7382157004897067063915220676230132902643632737 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (0, 2) then (2563195707811387 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (-2996186222833417 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-3482875521978183307688797892792422571952048737 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (-293183686727129 /
    20000000000000000 : ℚ) else
  if p = (1, 2) then (-1322425348301899 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (1557399994427 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-4827108031606907 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (13171359134213 /
    12500000000000000 : ℚ) else
  if p = (2, 2) then (183698965669761 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (49918120002869 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (12600765754950437 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (100929264087217 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-333096460085377 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-214213371805261 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf349_polynomial_eq :
    lowerPullbackPolynomial 7 3 majorizationTriangle349 radialPowerData10.radius
      (certifiedRadialHeight radialPowerData10 radialPowerData32)
      (certifiedRadialSlope radialPowerData10) 1 =
        planeArrayPolynomial majorizationArray349 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 3 majorizationTriangle349
    cellMatrix_7_3 cellMatrix_7_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf349_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray349 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf349_kernel {p : ℝ × ℝ} (hp : majorizationTriangle349.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 3 majorizationTriangle349
    radialPowerData10 radialPowerData32 radialPowerData10_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray349
    majorizationLeaf349_polynomial_eq majorizationLeaf349_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 350. -/
def majorizationTriangle350 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 350. -/
def majorizationArray350 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5082294176344418921028231724846047966351223453 /
    8913168282854737979273694412800000000000000000 : ℚ) else
  if p = (0, 1) then (58919841847367988913946442428672110526963276443 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (820498675153349 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (2606709954620969 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (150321371974913321201656722327156491629801967569 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-1010551399425439 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (1134977454906851 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (93344494106059 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-14250852979793699 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-1085988031834389 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (372617619006097 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (2908178358757 /
    60000000000000000 : ℚ) else
  if p = (3, 0) then (-765055828223029 /
    120000000000000000 : ℚ) else
  if p = (3, 1) then (-331230133231353 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (253841067898633 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-214213371805261 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf350_polynomial_eq :
    lowerPullbackPolynomial 7 3 majorizationTriangle350 radialPowerData11.radius
      (certifiedRadialHeight radialPowerData11 radialPowerData32)
      (certifiedRadialSlope radialPowerData11) 1 =
        planeArrayPolynomial majorizationArray350 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 3 majorizationTriangle350
    cellMatrix_7_3 cellMatrix_7_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf350_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray350 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf350_kernel {p : ℝ × ℝ} (hp : majorizationTriangle350.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 3 majorizationTriangle350
    radialPowerData11 radialPowerData32 radialPowerData11_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray350
    majorizationLeaf350_polynomial_eq majorizationLeaf350_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 351. -/
def majorizationTriangle351 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 351. -/
def majorizationArray351 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1991369928356673242869366477156037549102647112627 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-48667756975098473335473905854040767655403739803 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (586675112575093 /
    37500000000000000 : ℚ) else
  if p = (0, 3) then (-388004595009843 /
    40000000000000000 : ℚ) else
  if p = (1, 0) then (-86974425893632213311975412276926654426286329809 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-513651466280627 /
    12500000000000000 : ℚ) else
  if p = (1, 2) then (-82554246769217 /
    6250000000000000 : ℚ) else
  if p = (1, 3) then (3833562231621373 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-12863345201569567 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (4061871936579 /
    390625000000000 : ℚ) else
  if p = (2, 2) then (283535205675499 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-535814352187611 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (765055828223029 /
    120000000000000000 : ℚ) else
  if p = (3, 1) then (-331230133231353 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-253841067898633 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (1026164464995881 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf351_polynomial_eq :
    lowerPullbackPolynomial 7 4 majorizationTriangle351 radialPowerData11.radius
      (certifiedRadialHeight radialPowerData11 radialPowerData32)
      (certifiedRadialSlope radialPowerData11) 1 =
        planeArrayPolynomial majorizationArray351 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 4 majorizationTriangle351
    cellMatrix_7_4 cellMatrix_7_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf351_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray351 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf351_kernel {p : ℝ × ℝ} (hp : majorizationTriangle351.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 4 majorizationTriangle351
    radialPowerData11 radialPowerData32 radialPowerData11_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray351
    majorizationLeaf351_polynomial_eq majorizationLeaf351_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 352. -/
def majorizationTriangle352 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 352. -/
def majorizationArray352 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2419004487498998222849123858001834243972922517 /
    5942112188569825319515796275200000000000000000 : ℚ) else
  if p = (0, 1) then (70099612930754568954012423985003379430650168837 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-1884397136501563 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (4877842392635717 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (69056054541120530712182674391592684098055194117 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-5677871323449309 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-509863128584737 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (137070048624299 /
    50000000000000000 : ℚ) else
  if p = (2, 0) then (-3485438206279731 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-1249944678279631 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-41732194512171 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (72659823945869 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (-3618180539085721 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-186321542761247 /
    75000000000000000 : ℚ) else
  if p = (3, 2) then (-132320630649991 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (1026164464995881 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf352_polynomial_eq :
    lowerPullbackPolynomial 7 4 majorizationTriangle352 radialPowerData12.radius
      (certifiedRadialHeight radialPowerData12 radialPowerData32)
      (certifiedRadialSlope radialPowerData12) 1 =
        planeArrayPolynomial majorizationArray352 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 4 majorizationTriangle352
    cellMatrix_7_4 cellMatrix_7_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf352_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray352 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf352_kernel {p : ℝ × ℝ} (hp : majorizationTriangle352.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 4 majorizationTriangle352
    radialPowerData12 radialPowerData32 radialPowerData12_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray352
    majorizationLeaf352_polynomial_eq majorizationLeaf352_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 353. -/
def majorizationTriangle353 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 353. -/
def majorizationArray353 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (757142966890338438167897500289165540807382375871 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-52452315891553803236348691212889738651958134277 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-8073404974241447 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-1978619514277211 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-15584708915851499573515120470453057152464590679 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (-9668333022098547 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (1191826335006429 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (89443161531811 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-3538535139402127 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (2740517020369607 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-473302233860837 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-35960822152643 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (3618180539085721 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-186321542761247 /
    75000000000000000 : ℚ) else
  if p = (3, 2) then (132320630649991 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-45959915702017 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf353_polynomial_eq :
    lowerPullbackPolynomial 7 5 majorizationTriangle353 radialPowerData12.radius
      (certifiedRadialHeight radialPowerData12 radialPowerData32)
      (certifiedRadialSlope radialPowerData12) 1 =
        planeArrayPolynomial majorizationArray353 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 5 majorizationTriangle353
    cellMatrix_7_5 cellMatrix_7_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf353_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray353 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf353_kernel {p : ℝ × ℝ} (hp : majorizationTriangle353.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 5 majorizationTriangle353
    radialPowerData12 radialPowerData32 radialPowerData12_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray353
    majorizationLeaf353_polynomial_eq majorizationLeaf353_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 354. -/
def majorizationTriangle354 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 354. -/
def majorizationArray354 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (84342309134791285541931771043553382826722101 /
    316912650057057350374175801344000000000000000 : ℚ) else
  if p = (0, 1) then (4054179648219681329436491937850010395397097671 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (0, 2) then (-2326888284051849 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (221245573775143 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (4123631279938469646098020653153247285220247751 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (-901539428338341 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-660311053172867 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (15044792458813 /
    60000000000000000 : ℚ) else
  if p = (2, 0) then (-98858456527167 /
    8000000000000000 : ℚ) else
  if p = (2, 1) then (-750701995303261 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-58116342083103 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (1365345630911 /
    10000000000000000 : ℚ) else
  if p = (3, 0) then (-3512607920099443 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-1007249735192029 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-43736269119593 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (-45959915702017 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf354_polynomial_eq :
    lowerPullbackPolynomial 7 5 majorizationTriangle354 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray354 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 5 majorizationTriangle354
    cellMatrix_7_5 cellMatrix_7_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf354_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray354 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf354_kernel {p : ℝ × ℝ} (hp : majorizationTriangle354.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 5 majorizationTriangle354
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray354
    majorizationLeaf354_polynomial_eq majorizationLeaf354_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 355. -/
def majorizationTriangle355 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 355. -/
def majorizationArray355 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (139267219161995910944009429301557383975709491517 /
    356526731314189519170947776512000000000000000000 : ℚ) else
  if p = (0, 1) then (-3223153117041958005783046047975396713173911751 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (0, 2) then (-5026012244259329 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (2853185949275921 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-1071803437044262969085340844275738931617170157 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (1, 1) then (-438521929218141 /
    12500000000000000 : ℚ) else
  if p = (1, 2) then (730077909800931 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-738642604184731 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1365874019954621 /
    75000000000000000 : ℚ) else
  if p = (2, 1) then (175795173049529 /
    20000000000000000 : ℚ) else
  if p = (2, 2) then (-12731576400337 /
    5000000000000000 : ℚ) else
  if p = (2, 3) then (-17912403051199 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (3512607920099443 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-1007249735192029 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (43736269119593 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (313404130689341 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf355_polynomial_eq :
    lowerPullbackPolynomial 7 6 majorizationTriangle355 radialPowerData13.radius
      (certifiedRadialHeight radialPowerData13 radialPowerData32)
      (certifiedRadialSlope radialPowerData13) 1 =
        planeArrayPolynomial majorizationArray355 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 6 majorizationTriangle355
    cellMatrix_7_6 cellMatrix_7_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf355_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray355 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf355_kernel {p : ℝ × ℝ} (hp : majorizationTriangle355.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 6 majorizationTriangle355
    radialPowerData13 radialPowerData32 radialPowerData13_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray355
    majorizationLeaf355_polynomial_eq majorizationLeaf355_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 356. -/
def majorizationTriangle356 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 356. -/
def majorizationArray356 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (9395485380106795367869223757356843176917789449 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (25238347177762977613781236130819099778623022841 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 2) then (-243349591755923 /
    24000000000000000 : ℚ) else
  if p = (0, 3) then (-14014454035273 /
    28125000000000000 : ℚ) else
  if p = (1, 0) then (25346535272061453660017853055606102005426497273 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (1, 1) then (-3648138314943759 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-199247773575079 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-115265819899447 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-1147706331447229 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (-465030302110373 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (4910017222627 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-147745863819071 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-7605765010451 /
    9375000000000000 : ℚ) else
  if p = (3, 1) then (-42747152217793 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (-88680912714551 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (313404130689341 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf356_polynomial_eq :
    lowerPullbackPolynomial 7 6 majorizationTriangle356 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray356 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 6 majorizationTriangle356
    cellMatrix_7_6 cellMatrix_7_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf356_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray356 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf356_kernel {p : ℝ × ℝ} (hp : majorizationTriangle356.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 6 majorizationTriangle356
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray356
    majorizationLeaf356_polynomial_eq majorizationLeaf356_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 357. -/
def majorizationTriangle357 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 357. -/
def majorizationArray357 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (145284859308372384895994661587938886140482211123 /
    570442770102703230673516442419200000000000000000 : ℚ) else
  if p = (0, 1) then (-4249303799665227686427927571434386721180655973 /
    38029518006846882044901096161280000000000000000 : ℚ) else
  if p = (0, 2) then (-7198838539242737 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (7605765010451 /
    9375000000000000 : ℚ) else
  if p = (1, 0) then (-4249303799665227686427927571434386721180655973 /
    38029518006846882044901096161280000000000000000 : ℚ) else
  if p = (1, 1) then (-4834681832471263 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (721513215417131 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-42747152217793 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-7198838539242737 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (721513215417131 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-527175459064679 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (88680912714551 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (7605765010451 /
    9375000000000000 : ℚ) else
  if p = (3, 1) then (-42747152217793 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (88680912714551 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-132222068294741 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf357_polynomial_eq :
    lowerPullbackPolynomial 7 7 majorizationTriangle357 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray357 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 7 majorizationTriangle357
    cellMatrix_7_7 cellMatrix_7_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf357_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray357 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf357_kernel {p : ℝ × ℝ} (hp : majorizationTriangle357.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 7 majorizationTriangle357
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray357
    majorizationLeaf357_polynomial_eq majorizationLeaf357_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 358. -/
def majorizationTriangle358 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 358. -/
def majorizationArray358 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2198120070034756318966429111266331291800157 /
    14261069252567580766837911060480000000000000000 : ℚ) else
  if p = (0, 1) then (48970742425454087 /
    375000000000000000 : ℚ) else
  if p = (0, 2) then (-1246655959400627 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-365705318765189 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (48970742425454087 /
    375000000000000000 : ℚ) else
  if p = (1, 1) then (-226997083948651 /
    12500000000000000 : ℚ) else
  if p = (1, 2) then (22882850226217 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (-25487371692321 /
    40000000000000000 : ℚ) else
  if p = (2, 0) then (-1246655959400627 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (22882850226217 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (-40812695071421 /
    12500000000000000 : ℚ) else
  if p = (2, 3) then (219304379455121 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-365705318765189 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-25487371692321 /
    40000000000000000 : ℚ) else
  if p = (3, 2) then (219304379455121 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-132222068294741 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf358_polynomial_eq :
    lowerPullbackPolynomial 7 7 majorizationTriangle358 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray358 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 7 7 majorizationTriangle358
    cellMatrix_7_7 cellMatrix_7_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf358_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray358 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf358_kernel {p : ℝ × ℝ} (hp : majorizationTriangle358.Contains p) :
    (1 : ℝ) ≤ kernel (((7 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 7 7 majorizationTriangle358
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray358
    majorizationLeaf358_polynomial_eq majorizationLeaf358_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
