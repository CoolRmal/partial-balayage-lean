/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices12

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

/-- The actual closed rational triangle of majorization leaf 507. -/
def majorizationTriangle507 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 507. -/
def majorizationArray507 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1250715315637836799552670530765227076404729040247 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-16097700647623077125420536573665884674473641603 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (-4708576494038347 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-344192056094033 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-44852098851165932054722391059362101455021298569 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-1178330189206797 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (233961774448061 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (65143413820013 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (642591567841511 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (525770813254143 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (25833532664957 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (71688922365419 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-1877971340046169 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-378421090255193 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-5277607397969 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (-5061957955181 /
    28125000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf507_polynomial_eq :
    lowerPullbackPolynomial 11 6 majorizationTriangle507 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray507 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 6 majorizationTriangle507
    cellMatrix_11_6 cellMatrix_11_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf507_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray507 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf507_kernel {p : ℝ × ℝ} (hp : majorizationTriangle507.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 6 majorizationTriangle507
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray507
    majorizationLeaf507_polynomial_eq majorizationLeaf507_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 508. -/
def majorizationTriangle508 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 508. -/
def majorizationArray508 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (48226302063445752571658340390983222570570037883 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (102534684318934203029451966135338045575354987303 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-4471489544354011 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (515910934664873 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (80434874539520513310101498868975133461781754663 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (184583591503499 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-430552441669073 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (57103879626981 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-903892658217799 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-37342172313847 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-21890609272043 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (108898542035327 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (379596003434763 /
    200000000000000000 : ℚ) else
  if p = (3, 1) then (-251720824455489 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (116784448707143 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-5061957955181 /
    28125000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf508_polynomial_eq :
    lowerPullbackPolynomial 11 6 majorizationTriangle508 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray508 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 6 majorizationTriangle508
    cellMatrix_11_6 cellMatrix_11_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf508_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray508 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf508_kernel {p : ℝ × ℝ} (hp : majorizationTriangle508.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 6 majorizationTriangle508
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray508
    majorizationLeaf508_polynomial_eq majorizationLeaf508_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 509. -/
def majorizationTriangle509 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 509. -/
def majorizationArray509 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2171473325784128869019194575948260954480340417709 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-102038021640946477886884140586219459183026713383 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-2870576331160223 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-1727439734770807 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-82983769255672342924447603038433050972520002343 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-322631613245331 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (149552594134037 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (285891100481423 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (628117843173767 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (396252322840157 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (120450149880607 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-2193958103873 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (-379596003434763 /
    200000000000000000 : ℚ) else
  if p = (3, 1) then (-251720824455489 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-116784448707143 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-12161761224517 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf509_polynomial_eq :
    lowerPullbackPolynomial 11 7 majorizationTriangle509 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray509 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 7 majorizationTriangle509
    cellMatrix_11_7 cellMatrix_11_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf509_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray509 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf509_kernel {p : ℝ × ℝ} (hp : majorizationTriangle509.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 7 majorizationTriangle509
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray509
    majorizationLeaf509_polynomial_eq majorizationLeaf509_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 510. -/
def majorizationTriangle510 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 510. -/
def majorizationArray510 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (40295850604960246913772242841879030212424450331 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (13767471356215923449093710711392358893642279457 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (-19529723967119 /
    1875000000000000 : ℚ) else
  if p = (0, 3) then (592674041708023 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (8408593553061435391095718237633816750733617697 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (158775724974899 /
    20000000000000000 : ℚ) else
  if p = (1, 2) then (-486310608288209 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (108413754981469 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-71322679624807 /
    37500000000000000 : ℚ) else
  if p = (2, 1) then (1582043078489 /
    1562500000000000 : ℚ) else
  if p = (2, 2) then (-4074707500007 /
    6250000000000000 : ℚ) else
  if p = (2, 3) then (6979197880003 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (421567078162567 /
    112500000000000000 : ℚ) else
  if p = (3, 1) then (-734015463416921 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (181257553672973 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-12161761224517 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf510_polynomial_eq :
    lowerPullbackPolynomial 11 7 majorizationTriangle510 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray510 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 7 majorizationTriangle510
    cellMatrix_11_7 cellMatrix_11_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf510_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray510 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf510_kernel {p : ℝ × ℝ} (hp : majorizationTriangle510.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 7 majorizationTriangle510
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray510
    majorizationLeaf510_polynomial_eq majorizationLeaf510_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 511. -/
def majorizationTriangle511 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 511. -/
def majorizationArray511 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12631274516715921993213190514603692611279099277 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (0, 1) then (-4846829905400798895848338051978195520064572939 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 2) then (-153267202197701 /
    10000000000000000 : ℚ) else
  if p = (0, 3) then (-14608912499765459 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-9292531764053171279080055603044317844297706017 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (131182337752083 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (21772184730773 /
    5000000000000000 : ℚ) else
  if p = (1, 3) then (1615148716391767 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (729675830287 /
    78125000000000 : ℚ) else
  if p = (2, 1) then (5062117651149 /
    800000000000000 : ℚ) else
  if p = (2, 2) then (116062233672861 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-1576350570985169 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-421567078162567 /
    112500000000000000 : ℚ) else
  if p = (3, 1) then (-734015463416921 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-181257553672973 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (73642912324877 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf511_polynomial_eq :
    lowerPullbackPolynomial 11 8 majorizationTriangle511 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray511 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 8 majorizationTriangle511
    cellMatrix_11_8 cellMatrix_11_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf511_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray511 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf511_kernel {p : ℝ × ℝ} (hp : majorizationTriangle511.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 8 majorizationTriangle511
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray511
    majorizationLeaf511_polynomial_eq majorizationLeaf511_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 512. -/
def majorizationTriangle512 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 512. -/
def majorizationArray512 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (392698367760174529311024034703587741655278111 /
    891316828285473797927369441280000000000000000 : ℚ) else
  if p = (0, 1) then (8082879212545143429702324330044079136065789731 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (0, 2) then (-10903851610023389 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (4654339940545309 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (2761722862172704272477131721690962614747471651 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 1) then (5373030514756543 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-562530409686227 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (613343610618239 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-142756163298911 /
    24000000000000000 : ℚ) else
  if p = (2, 1) then (378469508076491 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (-1559455386335639 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (285812949267083 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (2014904254748447 /
    300000000000000000 : ℚ) else
  if p = (3, 1) then (-102288765843799 /
    30000000000000000 : ℚ) else
  if p = (3, 2) then (70061615461 /
    195312500000000 : ℚ) else
  if p = (3, 3) then (73642912324877 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf512_polynomial_eq :
    lowerPullbackPolynomial 11 8 majorizationTriangle512 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray512 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 8 majorizationTriangle512
    cellMatrix_11_8 cellMatrix_11_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf512_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray512 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf512_kernel {p : ℝ × ℝ} (hp : majorizationTriangle512.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 8 majorizationTriangle512
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray512
    majorizationLeaf512_polynomial_eq majorizationLeaf512_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 513. -/
def majorizationTriangle513 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 513. -/
def majorizationArray513 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (86961779429232309134249083886617995765336114593 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-10038860013254201093847326821961983835659640611 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (0, 2) then (-23804944631627519 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-3002133999351597 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-3252107293656962817336646481776451470625677091 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 1) then (7111950278645473 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (5716333538406221 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-19810660560079211 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (8520521446017907 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (6137111059741 /
    8000000000000000 : ℚ) else
  if p = (2, 2) then (-1344226103639447 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (15177957621627763 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-2014904254748447 /
    300000000000000000 : ℚ) else
  if p = (3, 1) then (-102288765843799 /
    30000000000000000 : ℚ) else
  if p = (3, 2) then (-70061615461 /
    195312500000000 : ℚ) else
  if p = (3, 3) then (-9775468355960687 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf513_polynomial_eq :
    lowerPullbackPolynomial 11 9 majorizationTriangle513 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray513 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 9 majorizationTriangle513
    cellMatrix_11_9 cellMatrix_11_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf513_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray513 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf513_kernel {p : ℝ × ℝ} (hp : majorizationTriangle513.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 9 majorizationTriangle513
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray513
    majorizationLeaf513_polynomial_eq majorizationLeaf513_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 514. -/
def majorizationTriangle514 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 514. -/
def majorizationArray514 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (203475225177017246475933516336303767560990787 /
    713053462628379038341895553024000000000000000 : ℚ) else
  if p = (0, 1) then (170490951270763347934809296128762364145412368463 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-388124616510793 /
    12000000000000000 : ℚ) else
  if p = (0, 3) then (944708801724029 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-21560259395334330843146534092788871875014137777 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (11801304822771029 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-770846354117719 /
    10000000000000000 : ℚ) else
  if p = (1, 3) then (2520855006784649 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-2704325013350789 /
    60000000000000000 : ℚ) else
  if p = (2, 1) then (9065097791967283 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-1834799082152059 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (4372979090293611 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (646043745524761 /
    15000000000000000 : ℚ) else
  if p = (3, 1) then (-30564522009016243 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (9811339903076719 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-9775468355960687 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf514_polynomial_eq :
    lowerPullbackPolynomial 11 9 majorizationTriangle514 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray514 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 9 majorizationTriangle514
    cellMatrix_11_9 cellMatrix_11_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf514_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray514 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf514_kernel {p : ℝ × ℝ} (hp : majorizationTriangle514.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 9 majorizationTriangle514
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray514
    majorizationLeaf514_polynomial_eq majorizationLeaf514_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 515. -/
def majorizationTriangle515 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 515. -/
def majorizationArray515 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (743508562800801678248567115046716705302918942669 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-90670974362848100541576526673695144297592267461 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-12706037656447973 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (225998219998453621 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-5193307071076877033596266290931542480489030341 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-79127700288831 /
    12500000000000000 : ℚ) else
  if p = (1, 2) then (-1409432702167299 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (2866351145143869 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (5048199932946343 /
    60000000000000000 : ℚ) else
  if p = (2, 1) then (33592850339139 /
    156250000000000 : ℚ) else
  if p = (2, 2) then (22094823380621921 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-136873415542826987 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-646043745524761 /
    15000000000000000 : ℚ) else
  if p = (3, 1) then (-30564522009016243 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-9811339903076719 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (11616337916029839 /
    100000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf515_polynomial_eq :
    lowerPullbackPolynomial 11 10 majorizationTriangle515 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray515 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 10 majorizationTriangle515
    cellMatrix_11_10 cellMatrix_11_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf515_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray515 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf515_kernel {p : ℝ × ℝ} (hp : majorizationTriangle515.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 10 majorizationTriangle515
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray515
    majorizationLeaf515_polynomial_eq majorizationLeaf515_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 516. -/
def majorizationTriangle516 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 516. -/
def majorizationArray516 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1868392446509731995881088650383351847473505923 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (146403512441891530044467078162262076277106237661 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (30862985339264933 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-50269216164804583 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-124159892484861435865022062621971367814267576099 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-1617231351434447 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (8127353615866177 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-11210739032337053 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-53248347911250889 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-4946737209468521 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (57542274288493643 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-14444133389142023 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (12690134293550701 /
    100000000000000000 : ℚ) else
  if p = (3, 1) then (7557239908395997 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (-12518836922506399 /
    50000000000000000 : ℚ) else
  if p = (3, 3) then (11616337916029839 /
    100000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf516_polynomial_eq :
    lowerPullbackPolynomial 11 10 majorizationTriangle516 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray516 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 10 majorizationTriangle516
    cellMatrix_11_10 cellMatrix_11_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf516_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray516 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf516_kernel {p : ℝ × ℝ} (hp : majorizationTriangle516.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 10 majorizationTriangle516
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray516
    majorizationLeaf516_polynomial_eq majorizationLeaf516_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 517. -/
def majorizationTriangle517 : RationalTriangle := ⟨
  (0, 0),
  ((1 / 4 : ℚ), 0),
  (0, (1 / 4 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 517. -/
def majorizationArray517 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (21696581852040022086011888294943388258568425241 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-3058703957042835029215466796659669017698986369 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (175174069372661729 /
    9600000000000000000 : ℚ) else
  if p = (0, 3) then (-12690134293550701 /
    6400000000000000000 : ℚ) else
  if p = (1, 0) then (-3058703957042835029215466796659669017698986369 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (-20855643812535669 /
    3200000000000000000 : ℚ) else
  if p = (1, 2) then (-5495273586241383 /
    12800000000000000000 : ℚ) else
  if p = (1, 3) then (7557239908395997 /
    38400000000000000000 : ℚ) else
  if p = (2, 0) then (175174069372661729 /
    9600000000000000000 : ℚ) else
  if p = (2, 1) then (-5495273586241383 /
    12800000000000000000 : ℚ) else
  if p = (2, 2) then (-18536753756316629 /
    10240000000000000000 : ℚ) else
  if p = (2, 3) then (12518836922506399 /
    51200000000000000000 : ℚ) else
  if p = (3, 0) then (-12690134293550701 /
    6400000000000000000 : ℚ) else
  if p = (3, 1) then (7557239908395997 /
    38400000000000000000 : ℚ) else
  if p = (3, 2) then (12518836922506399 /
    51200000000000000000 : ℚ) else
  if p = (3, 3) then (-90879386636130617 /
    2457600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf517_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle517 radialPowerData22.radius
      (certifiedRadialHeight radialPowerData22 radialPowerData32)
      (certifiedRadialSlope radialPowerData22) 0 =
        planeArrayPolynomial majorizationArray517 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle517
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf517_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray517 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf517_kernel {p : ℝ × ℝ} (hp : majorizationTriangle517.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle517
    radialPowerData22 radialPowerData32 radialPowerData22_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray517
    majorizationLeaf517_polynomial_eq majorizationLeaf517_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 518. -/
def majorizationTriangle518 : RationalTriangle := ⟨
  ((1 / 4 : ℚ), 0),
  ((1 / 2 : ℚ), 0),
  ((1 / 4 : ℚ), (1 / 4 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 518. -/
def majorizationArray518 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (136655654192607193810857288655082043234284547979 /
    11408855402054064613470328848384000000000000000000 : ℚ) else
  if p = (0, 1) then (-97569964884886153205177639591577430663095697753 /
    3802951800684688204490109616128000000000000000000 : ℚ) else
  if p = (0, 2) then (249634703135046083 /
    15360000000000000000 : ℚ) else
  if p = (0, 3) then (-3879323428941948841 /
    2457600000000000000000 : ℚ) else
  if p = (1, 0) then (44264929860525013733288128093044006538954882727 /
    3802951800684688204490109616128000000000000000000 : ℚ) else
  if p = (1, 1) then (-17371176502845889 /
    2560000000000000000 : ℚ) else
  if p = (1, 2) then (-1358336969124901 /
    409600000000000000 : ℚ) else
  if p = (1, 3) then (1412833538789566261 /
    2457600000000000000000 : ℚ) else
  if p = (2, 0) then (236136930103367149 /
    19200000000000000000 : ℚ) else
  if p = (2, 1) then (1030983161077307 /
    6400000000000000000 : ℚ) else
  if p = (2, 2) then (-13781814503515987 /
    12800000000000000000 : ℚ) else
  if p = (2, 3) then (109422004123971767 /
    819200000000000000000 : ℚ) else
  if p = (3, 0) then (-12690134293550701 /
    6400000000000000000 : ℚ) else
  if p = (3, 1) then (7557239908395997 /
    38400000000000000000 : ℚ) else
  if p = (3, 2) then (12518836922506399 /
    51200000000000000000 : ℚ) else
  if p = (3, 3) then (-90879386636130617 /
    2457600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf518_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle518 radialPowerData24.radius
      (certifiedRadialHeight radialPowerData24 radialPowerData32)
      (certifiedRadialSlope radialPowerData24) 0 =
        planeArrayPolynomial majorizationArray518 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle518
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf518_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray518 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf518_kernel {p : ℝ × ℝ} (hp : majorizationTriangle518.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle518
    radialPowerData24 radialPowerData32 radialPowerData24_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray518
    majorizationLeaf518_polynomial_eq majorizationLeaf518_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 519. -/
def majorizationTriangle519 : RationalTriangle := ⟨
  (0, (1 / 4 : ℚ)),
  ((1 / 4 : ℚ), (1 / 4 : ℚ)),
  (0, (1 / 2 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 519. -/
def majorizationArray519 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (136655654192607193810857288655082043234284547979 /
    11408855402054064613470328848384000000000000000000 : ℚ) else
  if p = (0, 1) then (44264929860525013733288128093044006538954882727 /
    3802951800684688204490109616128000000000000000000 : ℚ) else
  if p = (0, 2) then (236136930103367149 /
    19200000000000000000 : ℚ) else
  if p = (0, 3) then (-12690134293550701 /
    6400000000000000000 : ℚ) else
  if p = (1, 0) then (-97569964884886153205177639591577430663095697753 /
    3802951800684688204490109616128000000000000000000 : ℚ) else
  if p = (1, 1) then (-17371176502845889 /
    2560000000000000000 : ℚ) else
  if p = (1, 2) then (1030983161077307 /
    6400000000000000000 : ℚ) else
  if p = (1, 3) then (7557239908395997 /
    38400000000000000000 : ℚ) else
  if p = (2, 0) then (249634703135046083 /
    15360000000000000000 : ℚ) else
  if p = (2, 1) then (-1358336969124901 /
    409600000000000000 : ℚ) else
  if p = (2, 2) then (-13781814503515987 /
    12800000000000000000 : ℚ) else
  if p = (2, 3) then (12518836922506399 /
    51200000000000000000 : ℚ) else
  if p = (3, 0) then (-3879323428941948841 /
    2457600000000000000000 : ℚ) else
  if p = (3, 1) then (1412833538789566261 /
    2457600000000000000000 : ℚ) else
  if p = (3, 2) then (109422004123971767 /
    819200000000000000000 : ℚ) else
  if p = (3, 3) then (-90879386636130617 /
    2457600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf519_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle519 radialPowerData24.radius
      (certifiedRadialHeight radialPowerData24 radialPowerData32)
      (certifiedRadialSlope radialPowerData24) 0 =
        planeArrayPolynomial majorizationArray519 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle519
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf519_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray519 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf519_kernel {p : ℝ × ℝ} (hp : majorizationTriangle519.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle519
    radialPowerData24 radialPowerData32 radialPowerData24_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray519
    majorizationLeaf519_polynomial_eq majorizationLeaf519_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 520. -/
def majorizationTriangle520 : RationalTriangle := ⟨
  ((1 / 4 : ℚ), 0),
  ((1 / 4 : ℚ), (1 / 8 : ℚ)),
  ((1 / 8 : ℚ), (1 / 8 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 520. -/
def majorizationArray520 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (34583967391924354991383827860066761777279173391 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (1, 0) then (-12289683450532318429425568229624169041460234197 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (2, 0) then (249634703135046083 /
    61440000000000000000 : ℚ) else
  if p = (1, 1) then (241398586114867 /
    24576000000000000 : ℚ) else
  if p = (0, 2) then (2713856531174075681 /
    307200000000000000000 : ℚ) else
  if p = (3, 0) then (-3879323428941948841 /
    19660800000000000000000 : ℚ) else
  if p = (2, 1) then (-1162649490692146841 /
    6553600000000000000000 : ℚ) else
  if p = (1, 2) then (337198058435110091 /
    1310720000000000000000 : ℚ) else
  if p = (0, 3) then (9539607488384612231 /
    19660800000000000000000 : ℚ) else
  if p = (0, 1) then (-238694407383022899 /
    12800000000000000000 : ℚ) else
  if p = (3, 1) then (-1412833538789566261 /
    39321600000000000000000 : ℚ) else
  if p = (2, 2) then (-2294869667014589429 /
    13107200000000000000000 : ℚ) else
  if p = (1, 3) then (-10014380739856181599 /
    39321600000000000000000 : ℚ) else
  if p = (0, 4) then (-4542605277601979573 /
    39321600000000000000000 : ℚ) else
  if p = (3, 2) then (109422004123971767 /
    26214400000000000000000 : ℚ) else
  if p = (2, 3) then (127964621611812917 /
    26214400000000000000000 : ℚ) else
  if p = (1, 4) then (-72336769148289467 /
    26214400000000000000000 : ℚ) else
  if p = (0, 5) then (-90879386636130617 /
    26214400000000000000000 : ℚ) else
  if p = (3, 3) then (90879386636130617 /
    157286400000000000000000 : ℚ) else
  if p = (2, 4) then (90879386636130617 /
    52428800000000000000000 : ℚ) else
  if p = (1, 5) then (90879386636130617 /
    52428800000000000000000 : ℚ) else
  if p = (0, 6) then (90879386636130617 /
    157286400000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf520_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle520 radialPowerData23.radius
      (certifiedRadialHeight radialPowerData23 radialPowerData32)
      (certifiedRadialSlope radialPowerData23) 0 =
        planeArrayPolynomial majorizationArray520 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle520
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf520_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray520 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf520_kernel {p : ℝ × ℝ} (hp : majorizationTriangle520.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle520
    radialPowerData23 radialPowerData32 radialPowerData23_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray520
    majorizationLeaf520_polynomial_eq majorizationLeaf520_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 521. -/
def majorizationTriangle521 : RationalTriangle := ⟨
  ((1 / 4 : ℚ), (1 / 8 : ℚ)),
  ((1 / 4 : ℚ), (1 / 4 : ℚ)),
  ((1 / 8 : ℚ), (1 / 4 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 521. -/
def majorizationArray521 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (68809030306705361147372534660895846934974044939 /
    22817710804108129226940657696768000000000000000000 : ℚ) else
  if p = (1, 0) then (-13421875909778679703357519685668973355188371571 /
    2535301200456458802993406410752000000000000000000 : ℚ) else
  if p = (0, 1) then (-23694680811986772869 /
    2621440000000000000000 : ℚ) else
  if p = (2, 0) then (68245134716388900037 /
    19660800000000000000000 : ℚ) else
  if p = (1, 1) then (2944379546232901913 /
    314572800000000000000 : ℚ) else
  if p = (0, 2) then (701538203496954358523 /
    78643200000000000000000 : ℚ) else
  if p = (3, 0) then (-3879323428941948841 /
    19660800000000000000000 : ℚ) else
  if p = (2, 1) then (-3738132520173859943 /
    13107200000000000000000 : ℚ) else
  if p = (1, 2) then (-421450297396848119 /
    5242880000000000000000 : ℚ) else
  if p = (0, 3) then (37118004063959179571 /
    157286400000000000000000 : ℚ) else
  if p = (3, 1) then (-1412833538789566261 /
    39321600000000000000000 : ℚ) else
  if p = (2, 2) then (-4261473321657263557 /
    26214400000000000000000 : ℚ) else
  if p = (1, 3) then (-38249309340174579541 /
    157286400000000000000000 : ℚ) else
  if p = (0, 4) then (-18331803565389263243 /
    157286400000000000000000 : ℚ) else
  if p = (3, 2) then (109422004123971767 /
    26214400000000000000000 : ℚ) else
  if p = (2, 3) then (346808629859756451 /
    52428800000000000000000 : ℚ) else
  if p = (1, 4) then (370852349756823 /
    524288000000000000000 : ℚ) else
  if p = (0, 5) then (-90879386636130617 /
    52428800000000000000000 : ℚ) else
  if p = (3, 3) then (90879386636130617 /
    157286400000000000000000 : ℚ) else
  if p = (2, 4) then (90879386636130617 /
    52428800000000000000000 : ℚ) else
  if p = (1, 5) then (90879386636130617 /
    52428800000000000000000 : ℚ) else
  if p = (0, 6) then (90879386636130617 /
    157286400000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf521_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle521 radialPowerData24.radius
      (certifiedRadialHeight radialPowerData24 radialPowerData32)
      (certifiedRadialSlope radialPowerData24) 0 =
        planeArrayPolynomial majorizationArray521 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle521
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf521_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray521 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf521_kernel {p : ℝ × ℝ} (hp : majorizationTriangle521.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle521
    radialPowerData24 radialPowerData32 radialPowerData24_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray521
    majorizationLeaf521_polynomial_eq majorizationLeaf521_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 522. -/
def majorizationTriangle522 : RationalTriangle := ⟨
  ((1 / 8 : ℚ), (1 / 8 : ℚ)),
  ((1 / 8 : ℚ), (1 / 4 : ℚ)),
  (0, (1 / 4 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 522. -/
def majorizationArray522 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (7639000303444962393982607839104323784302953231 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (1, 0) then (-2949547878665909356032072603335895060030719957 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (2, 0) then (584663242134510644501 /
    157286400000000000000000 : ℚ) else
  if p = (1, 1) then (1505333024621284054699 /
    157286400000000000000000 : ℚ) else
  if p = (0, 2) then (1505333024621284054699 /
    157286400000000000000000 : ℚ) else
  if p = (3, 0) then (-35938510175313894553 /
    157286400000000000000000 : ℚ) else
  if p = (2, 1) then (-2652884798543849019 /
    5242880000000000000000 : ℚ) else
  if p = (1, 2) then (-2652884798543849019 /
    5242880000000000000000 : ℚ) else
  if p = (3, 1) then (-4065631945762211989 /
    157286400000000000000000 : ℚ) else
  if p = (2, 2) then (-122912728415167133 /
    819200000000000000000 : ℚ) else
  if p = (1, 3) then (-19533611909949877547 /
    78643200000000000000000 : ℚ) else
  if p = (0, 4) then (-19533611909949877547 /
    157286400000000000000000 : ℚ) else
  if p = (3, 2) then (309723394884074151 /
    52428800000000000000000 : ℚ) else
  if p = (2, 3) then (309723394884074151 /
    26214400000000000000000 : ℚ) else
  if p = (1, 4) then (309723394884074151 /
    52428800000000000000000 : ℚ) else
  if p = (3, 3) then (90879386636130617 /
    157286400000000000000000 : ℚ) else
  if p = (2, 4) then (90879386636130617 /
    52428800000000000000000 : ℚ) else
  if p = (1, 5) then (90879386636130617 /
    52428800000000000000000 : ℚ) else
  if p = (0, 6) then (90879386636130617 /
    157286400000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf522_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle522 radialPowerData23.radius
      (certifiedRadialHeight radialPowerData23 radialPowerData32)
      (certifiedRadialSlope radialPowerData23) 0 =
        planeArrayPolynomial majorizationArray522 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle522
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf522_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray522 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf522_kernel {p : ℝ × ℝ} (hp : majorizationTriangle522.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle522
    radialPowerData23 radialPowerData32 radialPowerData23_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray522
    majorizationLeaf522_polynomial_eq majorizationLeaf522_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 523. -/
def majorizationTriangle523 : RationalTriangle := ⟨
  ((1 / 4 : ℚ), (1 / 8 : ℚ)),
  ((1 / 8 : ℚ), (1 / 4 : ℚ)),
  ((1 / 8 : ℚ), (1 / 8 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 523. -/
def majorizationArray523 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (109260863904325985571949783585965765123249701 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (1, 0) then (-23694680811986772869 /
    2621440000000000000000 : ℚ) else
  if p = (2, 0) then (701538203496954358523 /
    78643200000000000000000 : ℚ) else
  if p = (3, 0) then (37118004063959179571 /
    157286400000000000000000 : ℚ) else
  if p = (0, 1) then (-1155630706750962262842905525947513413430923961 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (166745380108920809699 /
    19660800000000000000000 : ℚ) else
  if p = (2, 1) then (41332507037927660761 /
    52428800000000000000000 : ℚ) else
  if p = (4, 0) then (-18331803565389263243 /
    157286400000000000000000 : ℚ) else
  if p = (3, 1) then (-35077904921382473431 /
    157286400000000000000000 : ℚ) else
  if p = (0, 2) then (238423855804284480421 /
    78643200000000000000000 : ℚ) else
  if p = (1, 2) then (30594479931200702179 /
    52428800000000000000000 : ℚ) else
  if p = (2, 2) then (-6937244433918474059 /
    52428800000000000000000 : ℚ) else
  if p = (4, 1) then (-98296433631267077 /
    10485760000000000000000 : ℚ) else
  if p = (3, 2) then (-710326176404278919 /
    52428800000000000000000 : ℚ) else
  if p = (0, 3) then (35938510175313894553 /
    157286400000000000000000 : ℚ) else
  if p = (1, 3) then (-4065631945762211989 /
    157286400000000000000000 : ℚ) else
  if p = (2, 3) then (-309723394884074151 /
    52428800000000000000000 : ℚ) else
  if p = (5, 0) then (-90879386636130617 /
    52428800000000000000000 : ℚ) else
  if p = (6, 0) then (90879386636130617 /
    157286400000000000000000 : ℚ) else
  if p = (5, 1) then (90879386636130617 /
    52428800000000000000000 : ℚ) else
  if p = (4, 2) then (90879386636130617 /
    52428800000000000000000 : ℚ) else
  if p = (3, 3) then (90879386636130617 /
    157286400000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf523_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle523 radialPowerData23.radius
      (certifiedRadialHeight radialPowerData23 radialPowerData32)
      (certifiedRadialSlope radialPowerData23) 0 =
        planeArrayPolynomial majorizationArray523 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle523
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf523_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray523 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf523_kernel {p : ℝ × ℝ} (hp : majorizationTriangle523.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle523
    radialPowerData23 radialPowerData32 radialPowerData23_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray523
    majorizationLeaf523_polynomial_eq majorizationLeaf523_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 524. -/
def majorizationTriangle524 : RationalTriangle := ⟨
  ((1 / 2 : ℚ), 0),
  (1, 0),
  ((1 / 2 : ℚ), (1 / 2 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 524. -/
def majorizationArray524 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (189330284563024388444779014854584112610942404183 /
    5704427701027032306735164424192000000000000000000 : ℚ) else
  if p = (0, 1) then (-119152999242035216887708960220565913125716582621 /
    1901475900342344102245054808064000000000000000000 : ℚ) else
  if p = (0, 2) then (464786351163487577 /
    9600000000000000000 : ℚ) else
  if p = (0, 3) then (-278637908052074737 /
    38400000000000000000 : ℚ) else
  if p = (1, 0) then (118047825731080244278464967620594342989525851939 /
    1901475900342344102245054808064000000000000000000 : ℚ) else
  if p = (1, 1) then (-3758735498076211 /
    160000000000000000 : ℚ) else
  if p = (1, 2) then (-60622531600305331 /
    1600000000000000000 : ℚ) else
  if p = (1, 3) then (449181850906251253 /
    38400000000000000000 : ℚ) else
  if p = (2, 0) then (3048143036535271 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (9619206230550611 /
    1600000000000000000 : ℚ) else
  if p = (2, 2) then (-17570747246544751 /
    3200000000000000000 : ℚ) else
  if p = (2, 3) then (370852349756823 /
    512000000000000000 : ℚ) else
  if p = (3, 0) then (-12690134293550701 /
    800000000000000000 : ℚ) else
  if p = (3, 1) then (7557239908395997 /
    2400000000000000000 : ℚ) else
  if p = (3, 2) then (12518836922506399 /
    1600000000000000000 : ℚ) else
  if p = (3, 3) then (-90879386636130617 /
    38400000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf524_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle524 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray524 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle524
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf524_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray524 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf524_kernel {p : ℝ × ℝ} (hp : majorizationTriangle524.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle524
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray524
    majorizationLeaf524_polynomial_eq majorizationLeaf524_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 525. -/
def majorizationTriangle525 : RationalTriangle := ⟨
  (0, (1 / 2 : ℚ)),
  ((1 / 2 : ℚ), (1 / 2 : ℚ)),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 525. -/
def majorizationArray525 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (189330284563024388444779014854584112610942404183 /
    5704427701027032306735164424192000000000000000000 : ℚ) else
  if p = (0, 1) then (118047825731080244278464967620594342989525851939 /
    1901475900342344102245054808064000000000000000000 : ℚ) else
  if p = (0, 2) then (3048143036535271 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (-12690134293550701 /
    800000000000000000 : ℚ) else
  if p = (1, 0) then (-119152999242035216887708960220565913125716582621 /
    1901475900342344102245054808064000000000000000000 : ℚ) else
  if p = (1, 1) then (-3758735498076211 /
    160000000000000000 : ℚ) else
  if p = (1, 2) then (9619206230550611 /
    1600000000000000000 : ℚ) else
  if p = (1, 3) then (7557239908395997 /
    2400000000000000000 : ℚ) else
  if p = (2, 0) then (464786351163487577 /
    9600000000000000000 : ℚ) else
  if p = (2, 1) then (-60622531600305331 /
    1600000000000000000 : ℚ) else
  if p = (2, 2) then (-17570747246544751 /
    3200000000000000000 : ℚ) else
  if p = (2, 3) then (12518836922506399 /
    1600000000000000000 : ℚ) else
  if p = (3, 0) then (-278637908052074737 /
    38400000000000000000 : ℚ) else
  if p = (3, 1) then (449181850906251253 /
    38400000000000000000 : ℚ) else
  if p = (3, 2) then (370852349756823 /
    512000000000000000 : ℚ) else
  if p = (3, 3) then (-90879386636130617 /
    38400000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf525_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle525 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray525 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle525
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf525_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray525 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf525_kernel {p : ℝ × ℝ} (hp : majorizationTriangle525.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle525
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray525
    majorizationLeaf525_polynomial_eq majorizationLeaf525_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 526. -/
def majorizationTriangle526 : RationalTriangle := ⟨
  ((1 / 2 : ℚ), 0),
  ((1 / 2 : ℚ), (1 / 4 : ℚ)),
  ((1 / 4 : ℚ), (1 / 4 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 526. -/
def majorizationArray526 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (384972975185475597623053834428671089614887792887 /
    11408855402054064613470328848384000000000000000000 : ℚ) else
  if p = (1, 0) then (-120558486898824012769214016974481626580560480669 /
    3802951800684688204490109616128000000000000000000 : ℚ) else
  if p = (2, 0) then (464786351163487577 /
    38400000000000000000 : ℚ) else
  if p = (1, 1) then (577548416105773907 /
    19200000000000000000 : ℚ) else
  if p = (0, 2) then (934161923970881917 /
    38400000000000000000 : ℚ) else
  if p = (3, 0) then (-278637908052074737 /
    307200000000000000000 : ℚ) else
  if p = (2, 1) then (206342344750367911 /
    102400000000000000000 : ℚ) else
  if p = (1, 2) then (768276247397215447 /
    102400000000000000000 : ℚ) else
  if p = (0, 3) then (2016290245978901519 /
    307200000000000000000 : ℚ) else
  if p = (0, 1) then (-199593021341293489 /
    3200000000000000000 : ℚ) else
  if p = (3, 1) then (-449181850906251253 /
    614400000000000000000 : ℚ) else
  if p = (2, 2) then (-519464839892430257 /
    204800000000000000000 : ℚ) else
  if p = (1, 3) then (-378031865034032747 /
    122880000000000000000 : ℚ) else
  if p = (0, 4) then (-780946656399124217 /
    614400000000000000000 : ℚ) else
  if p = (3, 2) then (370852349756823 /
    16384000000000000000 : ℚ) else
  if p = (2, 3) then (-72336769148289467 /
    409600000000000000000 : ℚ) else
  if p = (1, 4) then (-172487464528340659 /
    409600000000000000000 : ℚ) else
  if p = (0, 5) then (-90879386636130617 /
    409600000000000000000 : ℚ) else
  if p = (3, 3) then (90879386636130617 /
    2457600000000000000000 : ℚ) else
  if p = (2, 4) then (90879386636130617 /
    819200000000000000000 : ℚ) else
  if p = (1, 5) then (90879386636130617 /
    819200000000000000000 : ℚ) else
  if p = (0, 6) then (90879386636130617 /
    2457600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf526_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle526 radialPowerData25.radius
      (certifiedRadialHeight radialPowerData25 radialPowerData32)
      (certifiedRadialSlope radialPowerData25) 0 =
        planeArrayPolynomial majorizationArray526 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle526
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf526_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray526 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf526_kernel {p : ℝ × ℝ} (hp : majorizationTriangle526.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle526
    radialPowerData25 radialPowerData32 radialPowerData25_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray526
    majorizationLeaf526_polynomial_eq majorizationLeaf526_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 527. -/
def majorizationTriangle527 : RationalTriangle := ⟨
  ((1 / 2 : ℚ), (1 / 4 : ℚ)),
  ((1 / 2 : ℚ), (1 / 2 : ℚ)),
  ((1 / 4 : ℚ), (1 / 2 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 527. -/
def majorizationArray527 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (148944092831204406070763960850959603292784847383 /
    11408855402054064613470328848384000000000000000000 : ℚ) else
  if p = (1, 0) then (-12480229505421615364106515441306088233989338527 /
    1267650600228229401496703205376000000000000000000 : ℚ) else
  if p = (0, 1) then (-6350479521515876217 /
    204800000000000000000 : ℚ) else
  if p = (2, 0) then (576475417030335281 /
    61440000000000000000 : ℚ) else
  if p = (1, 1) then (19610111899670426197 /
    614400000000000000000 : ℚ) else
  if p = (0, 2) then (36023521422711986891 /
    1228800000000000000000 : ℚ) else
  if p = (3, 0) then (-278637908052074737 /
    307200000000000000000 : ℚ) else
  if p = (2, 1) then (-36497161405515431 /
    204800000000000000000 : ℚ) else
  if p = (1, 2) then (204611911250180497 /
    81920000000000000000 : ℚ) else
  if p = (0, 3) then (8226543438896951027 /
    2457600000000000000000 : ℚ) else
  if p = (3, 1) then (-449181850906251253 /
    614400000000000000000 : ℚ) else
  if p = (2, 2) then (-1011115753553098789 /
    409600000000000000000 : ℚ) else
  if p = (1, 3) then (-8156040370551736693 /
    2457600000000000000000 : ℚ) else
  if p = (0, 4) then (-3886073252858148971 /
    2457600000000000000000 : ℚ) else
  if p = (3, 2) then (370852349756823 /
    16384000000000000000 : ℚ) else
  if p = (2, 3) then (-53794151660448317 /
    819200000000000000000 : ℚ) else
  if p = (1, 4) then (-40804038946105021 /
    204800000000000000000 : ℚ) else
  if p = (0, 5) then (-90879386636130617 /
    819200000000000000000 : ℚ) else
  if p = (3, 3) then (90879386636130617 /
    2457600000000000000000 : ℚ) else
  if p = (2, 4) then (90879386636130617 /
    819200000000000000000 : ℚ) else
  if p = (1, 5) then (90879386636130617 /
    819200000000000000000 : ℚ) else
  if p = (0, 6) then (90879386636130617 /
    2457600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf527_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle527 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray527 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle527
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf527_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray527 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf527_kernel {p : ℝ × ℝ} (hp : majorizationTriangle527.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle527
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray527
    majorizationLeaf527_polynomial_eq majorizationLeaf527_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 528. -/
def majorizationTriangle528 : RationalTriangle := ⟨
  ((1 / 4 : ℚ), (1 / 4 : ℚ)),
  ((1 / 4 : ℚ), (1 / 2 : ℚ)),
  (0, (1 / 2 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 528. -/
def majorizationArray528 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (9185728174464696351140421319669187126755799287 /
    11408855402054064613470328848384000000000000000000 : ℚ) else
  if p = (1, 0) then (9490059397526870828384523599716686315402983011 /
    3802951800684688204490109616128000000000000000000 : ℚ) else
  if p = (2, 0) then (28303582214781526757 /
    2457600000000000000000 : ℚ) else
  if p = (1, 1) then (85345036885425220171 /
    2457600000000000000000 : ℚ) else
  if p = (0, 2) then (85345036885425220171 /
    2457600000000000000000 : ℚ) else
  if p = (3, 0) then (-3879323428941948841 /
    2457600000000000000000 : ℚ) else
  if p = (2, 1) then (-1287741514740856551 /
    409600000000000000000 : ℚ) else
  if p = (1, 2) then (-1287741514740856551 /
    409600000000000000000 : ℚ) else
  if p = (3, 1) then (-1412833538789566261 /
    2457600000000000000000 : ℚ) else
  if p = (2, 2) then (-122912728415167133 /
    51200000000000000000 : ℚ) else
  if p = (1, 3) then (-4486977425138456123 /
    1228800000000000000000 : ℚ) else
  if p = (0, 4) then (-4486977425138456123 /
    2457600000000000000000 : ℚ) else
  if p = (3, 2) then (109422004123971767 /
    819200000000000000000 : ℚ) else
  if p = (2, 3) then (109422004123971767 /
    409600000000000000000 : ℚ) else
  if p = (1, 4) then (109422004123971767 /
    819200000000000000000 : ℚ) else
  if p = (3, 3) then (90879386636130617 /
    2457600000000000000000 : ℚ) else
  if p = (2, 4) then (90879386636130617 /
    819200000000000000000 : ℚ) else
  if p = (1, 5) then (90879386636130617 /
    819200000000000000000 : ℚ) else
  if p = (0, 6) then (90879386636130617 /
    2457600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf528_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle528 radialPowerData25.radius
      (certifiedRadialHeight radialPowerData25 radialPowerData32)
      (certifiedRadialSlope radialPowerData25) 0 =
        planeArrayPolynomial majorizationArray528 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle528
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf528_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray528 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf528_kernel {p : ℝ × ℝ} (hp : majorizationTriangle528.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle528
    radialPowerData25 radialPowerData32 radialPowerData25_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray528
    majorizationLeaf528_polynomial_eq majorizationLeaf528_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 529. -/
def majorizationTriangle529 : RationalTriangle := ⟨
  ((1 / 2 : ℚ), (1 / 4 : ℚ)),
  ((1 / 4 : ℚ), (1 / 2 : ℚ)),
  ((1 / 4 : ℚ), (1 / 4 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 529. -/
def majorizationArray529 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (944000224501655244748403720679470795757850861 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (1, 0) then (-6350479521515876217 /
    204800000000000000000 : ℚ) else
  if p = (2, 0) then (36023521422711986891 /
    1228800000000000000000 : ℚ) else
  if p = (3, 0) then (8226543438896951027 /
    2457600000000000000000 : ℚ) else
  if p = (0, 1) then (-26358838950713953015976526065563992107513598497 /
    1267650600228229401496703205376000000000000000000 : ℚ) else
  if p = (1, 1) then (8206704761520780347 /
    307200000000000000000 : ℚ) else
  if p = (2, 1) then (6180424326395146057 /
    819200000000000000000 : ℚ) else
  if p = (4, 0) then (-3886073252858148971 /
    2457600000000000000000 : ℚ) else
  if p = (3, 1) then (-7388252640880859191 /
    2457600000000000000000 : ℚ) else
  if p = (0, 2) then (8332805963977840117 /
    1228800000000000000000 : ℚ) else
  if p = (1, 2) then (3988316568271279363 /
    819200000000000000000 : ℚ) else
  if p = (2, 2) then (-1638337642270758827 /
    819200000000000000000 : ℚ) else
  if p = (4, 1) then (-291180777396233001 /
    819200000000000000000 : ℚ) else
  if p = (3, 2) then (-309723394884074151 /
    819200000000000000000 : ℚ) else
  if p = (0, 3) then (3879323428941948841 /
    2457600000000000000000 : ℚ) else
  if p = (1, 3) then (-1412833538789566261 /
    2457600000000000000000 : ℚ) else
  if p = (2, 3) then (-109422004123971767 /
    819200000000000000000 : ℚ) else
  if p = (5, 0) then (-90879386636130617 /
    819200000000000000000 : ℚ) else
  if p = (6, 0) then (90879386636130617 /
    2457600000000000000000 : ℚ) else
  if p = (5, 1) then (90879386636130617 /
    819200000000000000000 : ℚ) else
  if p = (4, 2) then (90879386636130617 /
    819200000000000000000 : ℚ) else
  if p = (3, 3) then (90879386636130617 /
    2457600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf529_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle529 radialPowerData25.radius
      (certifiedRadialHeight radialPowerData25 radialPowerData32)
      (certifiedRadialSlope radialPowerData25) 0 =
        planeArrayPolynomial majorizationArray529 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle529
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf529_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray529 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf529_kernel {p : ℝ × ℝ} (hp : majorizationTriangle529.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle529
    radialPowerData25 radialPowerData32 radialPowerData25_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray529
    majorizationLeaf529_polynomial_eq majorizationLeaf529_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 530. -/
def majorizationTriangle530 : RationalTriangle := ⟨
  (1, 1),
  ((1 / 2 : ℚ), 1),
  (1, (1 / 2 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 530. -/
def majorizationArray530 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1955732447296856663768869441600409472712437283 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (-5108084052722748341809821617488847842129708957 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (8895927032242849 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-13434810306225953 /
    4800000000000000000 : ℚ) else
  if p = (1, 0) then (-5108084052722748341809821617488847842129708957 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-3105985205593813 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-4351529446503707 /
    400000000000000000 : ℚ) else
  if p = (1, 3) then (58042885865345713 /
    9600000000000000000 : ℚ) else
  if p = (2, 0) then (8895927032242849 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-4351529446503707 /
    400000000000000000 : ℚ) else
  if p = (2, 2) then (-3243492127491071 /
    160000000000000000 : ℚ) else
  if p = (2, 3) then (40804038946105021 /
    6400000000000000000 : ℚ) else
  if p = (3, 0) then (-13434810306225953 /
    4800000000000000000 : ℚ) else
  if p = (3, 1) then (58042885865345713 /
    9600000000000000000 : ℚ) else
  if p = (3, 2) then (40804038946105021 /
    6400000000000000000 : ℚ) else
  if p = (3, 3) then (-90879386636130617 /
    38400000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf530_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle530 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray530 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle530
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf530_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray530 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf530_kernel {p : ℝ × ℝ} (hp : majorizationTriangle530.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle530
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray530
    majorizationLeaf530_polynomial_eq majorizationLeaf530_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 531. -/
def majorizationTriangle531 : RationalTriangle := ⟨
  ((1 / 2 : ℚ), 1),
  (0, 1),
  ((1 / 2 : ℚ), (1 / 2 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 531. -/
def majorizationArray531 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1575294786023417779337815423624216306854791897 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (-28729292769382320479088037145362782228266042203 /
    633825300114114700748351602688000000000000000000 : ℚ) else
  if p = (0, 2) then (93658978170750943 /
    19200000000000000000 : ℚ) else
  if p = (0, 3) then (278637908052074737 /
    38400000000000000000 : ℚ) else
  if p = (1, 0) then (26287989065070307683124827171214833203992640677 /
    633825300114114700748351602688000000000000000000 : ℚ) else
  if p = (1, 1) then (-22194622371543123 /
    640000000000000000 : ℚ) else
  if p = (1, 2) then (-206691724505029929 /
    6400000000000000000 : ℚ) else
  if p = (1, 3) then (449181850906251253 /
    38400000000000000000 : ℚ) else
  if p = (2, 0) then (4081216063888309 /
    192000000000000000 : ℚ) else
  if p = (2, 1) then (23230650293316057 /
    3200000000000000000 : ℚ) else
  if p = (2, 2) then (-7327568261327777 /
    6400000000000000000 : ℚ) else
  if p = (2, 3) then (-370852349756823 /
    512000000000000000 : ℚ) else
  if p = (3, 0) then (-13434810306225953 /
    4800000000000000000 : ℚ) else
  if p = (3, 1) then (58042885865345713 /
    9600000000000000000 : ℚ) else
  if p = (3, 2) then (40804038946105021 /
    6400000000000000000 : ℚ) else
  if p = (3, 3) then (-90879386636130617 /
    38400000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf531_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle531 radialPowerData27.radius
      (certifiedRadialHeight radialPowerData27 radialPowerData32)
      (certifiedRadialSlope radialPowerData27) 0 =
        planeArrayPolynomial majorizationArray531 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle531
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf531_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray531 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf531_kernel {p : ℝ × ℝ} (hp : majorizationTriangle531.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle531
    radialPowerData27 radialPowerData32 radialPowerData27_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray531
    majorizationLeaf531_polynomial_eq majorizationLeaf531_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 532. -/
def majorizationTriangle532 : RationalTriangle := ⟨
  (1, (1 / 2 : ℚ)),
  ((1 / 2 : ℚ), (1 / 2 : ℚ)),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 532. -/
def majorizationArray532 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1575294786023417779337815423624216306854791897 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (26287989065070307683124827171214833203992640677 /
    633825300114114700748351602688000000000000000000 : ℚ) else
  if p = (0, 2) then (4081216063888309 /
    192000000000000000 : ℚ) else
  if p = (0, 3) then (-13434810306225953 /
    4800000000000000000 : ℚ) else
  if p = (1, 0) then (-28729292769382320479088037145362782228266042203 /
    633825300114114700748351602688000000000000000000 : ℚ) else
  if p = (1, 1) then (-22194622371543123 /
    640000000000000000 : ℚ) else
  if p = (1, 2) then (23230650293316057 /
    3200000000000000000 : ℚ) else
  if p = (1, 3) then (58042885865345713 /
    9600000000000000000 : ℚ) else
  if p = (2, 0) then (93658978170750943 /
    19200000000000000000 : ℚ) else
  if p = (2, 1) then (-206691724505029929 /
    6400000000000000000 : ℚ) else
  if p = (2, 2) then (-7327568261327777 /
    6400000000000000000 : ℚ) else
  if p = (2, 3) then (40804038946105021 /
    6400000000000000000 : ℚ) else
  if p = (3, 0) then (278637908052074737 /
    38400000000000000000 : ℚ) else
  if p = (3, 1) then (449181850906251253 /
    38400000000000000000 : ℚ) else
  if p = (3, 2) then (-370852349756823 /
    512000000000000000 : ℚ) else
  if p = (3, 3) then (-90879386636130617 /
    38400000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf532_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle532 radialPowerData27.radius
      (certifiedRadialHeight radialPowerData27 radialPowerData32)
      (certifiedRadialSlope radialPowerData27) 0 =
        planeArrayPolynomial majorizationArray532 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle532
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf532_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray532 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf532_kernel {p : ℝ × ℝ} (hp : majorizationTriangle532.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle532
    radialPowerData27 radialPowerData32 radialPowerData27_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray532
    majorizationLeaf532_polynomial_eq majorizationLeaf532_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 533. -/
def majorizationTriangle533 : RationalTriangle := ⟨
  ((1 / 2 : ℚ), 1),
  ((1 / 2 : ℚ), (1 / 2 : ℚ)),
  (1, (1 / 2 : ℚ))⟩

/-- Candidate rational monomial coefficients of leaf 533. -/
def majorizationArray533 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1575294786023417779337815423624216306854791897 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (1, 0) then (-28729292769382320479088037145362782228266042203 /
    633825300114114700748351602688000000000000000000 : ℚ) else
  if p = (0, 1) then (-277766289604645307 /
    3200000000000000000 : ℚ) else
  if p = (2, 0) then (93658978170750943 /
    19200000000000000000 : ℚ) else
  if p = (1, 1) then (106644578435974447 /
    2400000000000000000 : ℚ) else
  if p = (0, 2) then (1167619255705875533 /
    19200000000000000000 : ℚ) else
  if p = (3, 0) then (278637908052074737 /
    38400000000000000000 : ℚ) else
  if p = (2, 1) then (138404271412426919 /
    2560000000000000000 : ℚ) else
  if p = (1, 2) then (1198327407245458681 /
    12800000000000000000 : ℚ) else
  if p = (0, 3) then (1905034541051854619 /
    38400000000000000000 : ℚ) else
  if p = (3, 1) then (-449181850906251253 /
    38400000000000000000 : ℚ) else
  if p = (2, 2) then (-463836987428906807 /
    12800000000000000000 : ℚ) else
  if p = (1, 3) then (-333529583063213987 /
    7680000000000000000 : ℚ) else
  if p = (0, 4) then (-725318803935600767 /
    38400000000000000000 : ℚ) else
  if p = (3, 2) then (-370852349756823 /
    512000000000000000 : ℚ) else
  if p = (2, 3) then (-109422004123971767 /
    12800000000000000000 : ℚ) else
  if p = (1, 4) then (-191030082016181809 /
    12800000000000000000 : ℚ) else
  if p = (0, 5) then (-90879386636130617 /
    12800000000000000000 : ℚ) else
  if p = (3, 3) then (90879386636130617 /
    38400000000000000000 : ℚ) else
  if p = (2, 4) then (90879386636130617 /
    12800000000000000000 : ℚ) else
  if p = (1, 5) then (90879386636130617 /
    12800000000000000000 : ℚ) else
  if p = (0, 6) then (90879386636130617 /
    38400000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf533_polynomial_eq :
    lowerPullbackPolynomial 11 11 majorizationTriangle533 radialPowerData27.radius
      (certifiedRadialHeight radialPowerData27 radialPowerData32)
      (certifiedRadialSlope radialPowerData27) 0 =
        planeArrayPolynomial majorizationArray533 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 11 11 majorizationTriangle533
    cellMatrix_11_11 cellMatrix_11_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf533_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray533 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf533_kernel {p : ℝ × ℝ} (hp : majorizationTriangle533.Contains p) :
    (0 : ℝ) ≤ kernel (((11 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 11 11 majorizationTriangle533
    radialPowerData27 radialPowerData32 radialPowerData27_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray533
    majorizationLeaf533_polynomial_eq majorizationLeaf533_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
