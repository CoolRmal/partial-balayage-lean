/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices26

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

/-- The actual closed rational triangle of majorization leaf 701. -/
def majorizationTriangle701 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 701. -/
def majorizationArray701 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (116000713590145950698669702648989000286058463733 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-9751798921480068165129655127635308843383089697 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (202324396246583 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-75473676883027 /
    150000000000000000 : ℚ) else
  if p = (1, 0) then (-10791106875568181912112991916153447534815046177 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (-114925867107567 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-37064281367531 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (747681550679 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-207678083801807 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-1547898084331 /
    10000000000000000 : ℚ) else
  if p = (2, 2) then (-15218521710001 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (7784035615729 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (76120685097379 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-1619112505061 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (62641427146363 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-46148686317191 /
    360000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf701_polynomial_eq :
    lowerPullbackPolynomial 18 1 majorizationTriangle701 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray701 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 1 majorizationTriangle701
    cellMatrix_18_1 cellMatrix_18_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf701_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray701 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf701_kernel {p : ℝ × ℝ} (hp : majorizationTriangle701.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 1 majorizationTriangle701
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray701
    majorizationLeaf701_polynomial_eq majorizationLeaf701_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 702. -/
def majorizationTriangle702 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 702. -/
def majorizationArray702 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2134073930137787138043762452445873451559889563 /
    4456584141427368989636847206400000000000000000 : ℚ) else
  if p = (0, 1) then (1521984450685817978629308431188331578257246817 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (0, 2) then (-528067510760929 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (987342734491009 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (5198829851997547078348298950179635540680056611 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 1) then (-7271870684357 /
    2000000000000000 : ℚ) else
  if p = (1, 2) then (17552128947391 /
    12500000000000000 : ℚ) else
  if p = (1, 3) then (-134344277994491 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-479589144729061 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (4958874207837 /
    6250000000000000 : ℚ) else
  if p = (2, 2) then (-7591741708261 /
    10000000000000000 : ℚ) else
  if p = (2, 3) then (184039217891581 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-1502474562433 /
    300000000000000000 : ℚ) else
  if p = (3, 1) then (-18926023303089 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (7004250184983 /
    25000000000000000 : ℚ) else
  if p = (3, 3) then (-46148686317191 /
    360000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf702_polynomial_eq :
    lowerPullbackPolynomial 18 1 majorizationTriangle702 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray702 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 1 majorizationTriangle702
    cellMatrix_18_1 cellMatrix_18_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf702_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray702 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf702_kernel {p : ℝ × ℝ} (hp : majorizationTriangle702.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 1 majorizationTriangle702
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray702
    majorizationLeaf702_polynomial_eq majorizationLeaf702_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 703. -/
def majorizationTriangle703 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 703. -/
def majorizationArray703 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (100673576724023048696014593009594137177611437473 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-1461933946180486524368190553752146822316362337 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (0, 2) then (-250517665051579 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-264895791720479 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-1669317410421048909895021366548565593251842657 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (1, 1) then (-261687629476333 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-9079149954213 /
    12500000000000000 : ℚ) else
  if p = (1, 3) then (-103703003393413 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-12102414210409 /
    7500000000000000 : ℚ) else
  if p = (2, 1) then (-180511339329 /
    800000000000000 : ℚ) else
  if p = (2, 2) then (4066792568593 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-49061251324569 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (1502474562433 /
    300000000000000000 : ℚ) else
  if p = (3, 1) then (-18926023303089 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (-7004250184983 /
    25000000000000000 : ℚ) else
  if p = (3, 3) then (79902076018661 /
    225000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf703_polynomial_eq :
    lowerPullbackPolynomial 18 2 majorizationTriangle703 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray703 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 2 majorizationTriangle703
    cellMatrix_18_2 cellMatrix_18_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf703_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray703 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf703_kernel {p : ℝ × ℝ} (hp : majorizationTriangle703.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 2 majorizationTriangle703
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray703
    majorizationLeaf703_polynomial_eq majorizationLeaf703_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 704. -/
def majorizationTriangle704 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 704. -/
def majorizationArray704 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (7192077727856688609896315881499931831771182731 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (23659303772785938760046324497922446379771503301 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-1964266060635367 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (908131039113509 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (80727627240442946334604645733524163768110311503 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-1047709097943751 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (7937593269959 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (80382032269487 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-1398701861730553 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-29679211194357 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (340198020010361 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-492032854175581 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (49185744312623 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (18945645945157 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (-1840291420741 /
    2343750000000000 : ℚ) else
  if p = (3, 3) then (79902076018661 /
    225000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf704_polynomial_eq :
    lowerPullbackPolynomial 18 2 majorizationTriangle704 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray704 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 2 majorizationTriangle704
    cellMatrix_18_2 cellMatrix_18_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf704_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray704 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf704_kernel {p : ℝ × ℝ} (hp : majorizationTriangle704.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 2 majorizationTriangle704
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray704
    majorizationLeaf704_polynomial_eq majorizationLeaf704_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 705. -/
def majorizationTriangle705 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 705. -/
def majorizationArray705 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1386578075165290320028938344972466255086562529229 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-66156547298692189507233360887777148993838803023 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-259144541052919 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (-1261474048461367 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-76606715795538096573264623256273456243868985423 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-183522212176179 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-248969402660821 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (77661491682631 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-1201958884480061 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-159777248257213 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-26183316739867 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (498892265108087 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-49185744312623 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (18945645945157 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (1840291420741 /
    2343750000000000 : ℚ) else
  if p = (3, 3) then (-499419441460451 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf705_polynomial_eq :
    lowerPullbackPolynomial 18 3 majorizationTriangle705 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray705 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 3 majorizationTriangle705
    cellMatrix_18_3 cellMatrix_18_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf705_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray705 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf705_kernel {p : ℝ × ℝ} (hp : majorizationTriangle705.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 3 majorizationTriangle705
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray705
    majorizationLeaf705_polynomial_eq majorizationLeaf705_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 706. -/
def majorizationTriangle706 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 706. -/
def majorizationArray706 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5839402768811152509358116537230041046984812163 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (24845790968904893653528449968105163500610942367 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-8053253074783 /
    1200000000000000 : ℚ) else
  if p = (0, 3) then (2062360476756133 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (27587075895456354166373745523510428106915607967 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-144641633707099 /
    10000000000000000 : ℚ) else
  if p = (1, 2) then (902717804924217 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-1765747643498639 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1393347275885509 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (89377456621977 /
    10000000000000000 : ℚ) else
  if p = (2, 2) then (-1078713181822129 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (2497624383654619 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (6057732182647 /
    9000000000000000 : ℚ) else
  if p = (3, 1) then (-19425322728039 /
    6250000000000000 : ℚ) else
  if p = (3, 2) then (252540204505301 /
    60000000000000000 : ℚ) else
  if p = (3, 3) then (-499419441460451 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf706_polynomial_eq :
    lowerPullbackPolynomial 18 3 majorizationTriangle706 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray706 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 3 majorizationTriangle706
    cellMatrix_18_3 cellMatrix_18_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf706_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray706 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf706_kernel {p : ℝ × ℝ} (hp : majorizationTriangle706.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 3 majorizationTriangle706
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray706
    majorizationLeaf706_polynomial_eq majorizationLeaf706_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 707. -/
def majorizationTriangle707 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 707. -/
def majorizationArray707 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (390420272232903472733923993284745668852572754301 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 1) then (-22109418406945013844549793741226169415181039007 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-426199458954327 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (-237607144328599 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (-75849612092694476281250389560828768171377909981 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-295641347788661 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (-1951285109 /
    24414062500000 : ℚ) else
  if p = (1, 3) then (-470193781786711 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-262524685873603 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (19320462363051 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (22998480088047 /
    12500000000000000 : ℚ) else
  if p = (2, 3) then (-689820592391723 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (-6057732182647 /
    9000000000000000 : ℚ) else
  if p = (3, 1) then (-19425322728039 /
    6250000000000000 : ℚ) else
  if p = (3, 2) then (-252540204505301 /
    60000000000000000 : ℚ) else
  if p = (3, 3) then (12599445748002941 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf707_polynomial_eq :
    lowerPullbackPolynomial 18 4 majorizationTriangle707 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray707 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 4 majorizationTriangle707
    cellMatrix_18_4 cellMatrix_18_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf707_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray707 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf707_kernel {p : ℝ × ℝ} (hp : majorizationTriangle707.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 4 majorizationTriangle707
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray707
    majorizationLeaf707_polynomial_eq majorizationLeaf707_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 708. -/
def majorizationTriangle708 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 708. -/
def majorizationArray708 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (17359131354207614228635906633981653956905004579 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (21810210338698205926988234299087555052599015523 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-7248210434158559 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (357953766307451 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (7641101410581496718801723207817310822274705441 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (1, 1) then (-260719602423307 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-3394670271873879 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (1733368627240771 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-4781457661586363 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-3737761518707993 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (7682737014791791 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-3280054459478683 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (594266589786907 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (5683810676005177 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-3358014567649977 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (12599445748002941 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf708_polynomial_eq :
    lowerPullbackPolynomial 18 4 majorizationTriangle708 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray708 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 4 majorizationTriangle708
    cellMatrix_18_4 cellMatrix_18_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf708_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray708 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf708_kernel {p : ℝ × ℝ} (hp : majorizationTriangle708.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 4 majorizationTriangle708
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray708
    majorizationLeaf708_polynomial_eq majorizationLeaf708_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 709. -/
def majorizationTriangle709 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 709. -/
def majorizationArray709 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (237385074416587553139628266714650073136285136519 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 1) then (-18070534935377433204757511205727468247993841763 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-2229026954177377 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-477187117750381 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (-19841282934358624049569324154222838310821197923 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-193456898345459 /
    12500000000000000 : ℚ) else
  if p = (1, 2) then (-474190013689943 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (468694386362161 /
    50000000000000000 : ℚ) else
  if p = (2, 0) then (-1499328946112821 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-60814036165537 /
    6250000000000000 : ℚ) else
  if p = (2, 2) then (-119565334407907 /
    10000000000000000 : ℚ) else
  if p = (2, 3) then (1765702369691711 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-594266589786907 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (5683810676005177 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (3358014567649977 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-4603347331174247 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf709_polynomial_eq :
    lowerPullbackPolynomial 18 5 majorizationTriangle709 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray709 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 5 majorizationTriangle709
    cellMatrix_18_5 cellMatrix_18_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf709_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray709 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf709_kernel {p : ℝ × ℝ} (hp : majorizationTriangle709.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 5 majorizationTriangle709
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray709
    majorizationLeaf709_polynomial_eq majorizationLeaf709_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 710. -/
def majorizationTriangle710 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 710. -/
def majorizationArray710 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5423824260236552805048575849301710062647026413 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (76898579299952257228601053638133052910976926169 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (10924223435782267 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-1009579659441157 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (26171591811281212990984018485170688268955997683 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (935683923446441 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-2587347357474861 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-134553819066503 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (12454168170017773 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-2077365779396359 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-373725310164137 /
    8000000000000000 : ℚ) else
  if p = (2, 3) then (354705620185317 /
    12500000000000000 : ℚ) else
  if p = (3, 0) then (-5956893126819707 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-1788185905140443 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (5848680094698517 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-4603347331174247 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf710_polynomial_eq :
    lowerPullbackPolynomial 18 5 majorizationTriangle710 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray710 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 5 majorizationTriangle710
    cellMatrix_18_5 cellMatrix_18_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf710_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray710 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf710_kernel {p : ℝ × ℝ} (hp : majorizationTriangle710.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 5 majorizationTriangle710
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray710
    majorizationLeaf710_polynomial_eq majorizationLeaf710_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 711. -/
def majorizationTriangle711 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 711. -/
def majorizationArray711 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (700336296901797354366022838314564627863281102747 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-28809896200111047109584472189750387108569601523 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-91514707685713 /
    7500000000000000 : ℚ) else
  if p = (0, 3) then (19319921447854889 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-89666388020102927889112349782549252002796569049 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-316124461675239 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (46594657269827 /
    2500000000000000 : ℚ) else
  if p = (1, 3) then (-1194783465169877 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1354127802610337 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (1932775842268401 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (4101453764996063 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-720058544844619 /
    24000000000000000 : ℚ) else
  if p = (3, 0) then (5956893126819707 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-1788185905140443 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-5848680094698517 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (30977479862572433 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf711_polynomial_eq :
    lowerPullbackPolynomial 18 6 majorizationTriangle711 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray711 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 6 majorizationTriangle711
    cellMatrix_18_6 cellMatrix_18_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf711_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray711 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf711_kernel {p : ℝ × ℝ} (hp : majorizationTriangle711.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 6 majorizationTriangle711
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray711
    majorizationLeaf711_polynomial_eq majorizationLeaf711_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 712. -/
def majorizationTriangle712 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 712. -/
def majorizationArray712 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1248365454903187608124692249455179408862541557 /
    14261069252567580766837911060480000000000000000 : ℚ) else
  if p = (0, 1) then (24928818773831023951806854637696346212639511367 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (3632883487353533 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (3645669974214367 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (24928818773831023951806854637696346212639511367 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (3632883487353533 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (3632883487353533 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-3110115422414197 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (3632883487353533 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (3632883487353533 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (3632883487353533 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-6488008120728479 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (2288629831169107 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (-245949442114963 /
    25000000000000000 : ℚ) else
  if p = (3, 2) then (-6715719789238441 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (30977479862572433 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf712_polynomial_eq :
    lowerPullbackPolynomial 18 6 majorizationTriangle712 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray712 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 6 majorizationTriangle712
    cellMatrix_18_6 cellMatrix_18_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf712_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray712 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf712_kernel {p : ℝ × ℝ} (hp : majorizationTriangle712.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 6 majorizationTriangle712
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray712
    majorizationLeaf712_polynomial_eq majorizationLeaf712_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
