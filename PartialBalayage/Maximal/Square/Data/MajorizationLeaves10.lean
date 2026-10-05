/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices10

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

/-- The actual closed rational triangle of majorization leaf 470. -/
def majorizationTriangle470 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 470. -/
def majorizationArray470 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (41270010592977023139327201299664638206162995989 /
    356526731314189519170947776512000000000000000000 : ℚ) else
  if p = (0, 1) then (-162067505304247423 /
    1500000000000000000 : ℚ) else
  if p = (0, 2) then (-519066177657623 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (-14240224210033 /
    22500000000000000 : ℚ) else
  if p = (1, 0) then (-41893764500824327 /
    375000000000000000 : ℚ) else
  if p = (1, 1) then (-255078062885763 /
    20000000000000000 : ℚ) else
  if p = (1, 2) then (30456251850653 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (38511680783 /
    1200000000000000 : ℚ) else
  if p = (2, 0) then (-768017998790467 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (264093069956329 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-2864940675421 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (19626789172669 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (46349893255873 /
    37500000000000000 : ℚ) else
  if p = (3, 1) then (-1333865563219 /
    12500000000000000 : ℚ) else
  if p = (3, 2) then (3936370867727 /
    50000000000000000 : ℚ) else
  if p = (3, 3) then (-88450311736759 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf470_polynomial_eq :
    lowerPullbackPolynomial 10 5 majorizationTriangle470 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray470 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 5 majorizationTriangle470
    cellMatrix_10_5 cellMatrix_10_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf470_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray470 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf470_kernel {p : ℝ × ℝ} (hp : majorizationTriangle470.Contains p) :
    (1 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 5 majorizationTriangle470
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray470
    majorizationLeaf470_polynomial_eq majorizationLeaf470_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 471. -/
def majorizationTriangle471 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 471. -/
def majorizationArray471 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (31509121371040124073486014472219713148583988843 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (36618890316687366589605980742447281346702608611 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-4708576494038347 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (311459752430957 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (102974664766655501125739504904070738903308573353 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-1178330189206797 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-233961774448061 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (87819842036093 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (642591567841511 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-525770813254143 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (25833532664957 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (3314385015361 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-2085977274679781 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-58002957945823 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (8242772264807 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (-88450311736759 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf471_polynomial_eq :
    lowerPullbackPolynomial 10 5 majorizationTriangle471 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray471 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 5 majorizationTriangle471
    cellMatrix_10_5 cellMatrix_10_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf471_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray471 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf471_kernel {p : ℝ × ℝ} (hp : majorizationTriangle471.Contains p) :
    (0 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 5 majorizationTriangle471
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray471
    majorizationLeaf471_polynomial_eq majorizationLeaf471_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 472. -/
def majorizationTriangle472 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 472. -/
def majorizationArray472 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (314378113555869242237000130019249087566165506771 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-101663994124671538103620954095109051665902344873 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-220489473252651 /
    25000000000000000 : ℚ) else
  if p = (0, 3) then (-72240262713941 /
    180000000000000000 : ℚ) else
  if p = (1, 0) then (-33901918600985796328800377441691344936029784291 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-1143937386830453 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (2204388246783 /
    3125000000000000 : ℚ) else
  if p = (1, 3) then (-112696800843229 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-48112856894609 /
    20000000000000000 : ℚ) else
  if p = (2, 1) then (291886885599983 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (523807765539 /
    1562500000000000 : ℚ) else
  if p = (2, 3) then (37735124205107 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (2085977274679781 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-58002957945823 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-8242772264807 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (139596518686043 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf472_polynomial_eq :
    lowerPullbackPolynomial 10 6 majorizationTriangle472 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray472 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 6 majorizationTriangle472
    cellMatrix_10_6 cellMatrix_10_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf472_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray472 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf472_kernel {p : ℝ × ℝ} (hp : majorizationTriangle472.Contains p) :
    (0 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 6 majorizationTriangle472
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray472
    majorizationLeaf472_polynomial_eq majorizationLeaf472_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 473. -/
def majorizationTriangle473 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 473. -/
def majorizationArray473 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (54691318138706177277894965277645001595305093771 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (56572230341169639621814245117714810133309969289 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-2870576331160223 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (344192056094033 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (47045104148532572140595976343821606028056613769 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-322631613245331 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-149552594134037 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (65143413820013 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (628117843173767 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-396252322840157 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (120450149880607 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-71688922365419 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-308467733689 /
    288000000000000 : ℚ) else
  if p = (3, 1) then (-16683238157 /
    12000000000000000 : ℚ) else
  if p = (3, 2) then (-12297832170251 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (139596518686043 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf473_polynomial_eq :
    lowerPullbackPolynomial 10 6 majorizationTriangle473 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray473 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 6 majorizationTriangle473
    cellMatrix_10_6 cellMatrix_10_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf473_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray473 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf473_kernel {p : ℝ × ℝ} (hp : majorizationTriangle473.Contains p) :
    (0 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 6 majorizationTriangle473
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray473
    majorizationLeaf473_polynomial_eq majorizationLeaf473_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 474. -/
def majorizationTriangle474 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 474. -/
def majorizationArray474 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1239405971693125979966856144889855982484852002167 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-53154218250993152517245438272796513835885155209 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-3007074992601517 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-94677246788001 /
    40000000000000000 : ℚ) else
  if p = (1, 0) then (-49498815719654073624697014330858146647995470729 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-111555333987957 /
    10000000000000000 : ℚ) else
  if p = (1, 2) then (-42156376946173 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-115581199474251 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (292274018569409 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (198334701897041 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (71258821199603 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (309100543933697 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (308467733689 /
    288000000000000 : ℚ) else
  if p = (3, 1) then (-16683238157 /
    12000000000000000 : ℚ) else
  if p = (3, 2) then (12297832170251 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (-936077464216583 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf474_polynomial_eq :
    lowerPullbackPolynomial 10 7 majorizationTriangle474 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray474 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 7 majorizationTriangle474
    cellMatrix_10_7 cellMatrix_10_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf474_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray474 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf474_kernel {p : ℝ × ℝ} (hp : majorizationTriangle474.Contains p) :
    (0 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 7 majorizationTriangle474
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray474
    majorizationLeaf474_polynomial_eq majorizationLeaf474_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 475. -/
def majorizationTriangle475 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 475. -/
def majorizationArray475 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5090536464585325356599368036685759341357645667 /
    7922816251426433759354395033600000000000000000 : ℚ) else
  if p = (0, 1) then (41902311909509423873138684026916071214235717901 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-153267202197701 /
    10000000000000000 : ℚ) else
  if p = (0, 3) then (1727439734770807 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (83723272111334468351696383657626063915539051303 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (131182337752083 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (-21772184730773 /
    5000000000000000 : ℚ) else
  if p = (1, 3) then (285891100481423 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (729675830287 /
    78125000000000 : ℚ) else
  if p = (2, 1) then (-5062117651149 /
    800000000000000 : ℚ) else
  if p = (2, 2) then (116062233672861 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (2193958103873 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (-1284491357702141 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-740146311400417 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (33507792274183 /
    24000000000000000 : ℚ) else
  if p = (3, 3) then (-936077464216583 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf475_polynomial_eq :
    lowerPullbackPolynomial 10 7 majorizationTriangle475 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray475 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 7 majorizationTriangle475
    cellMatrix_10_7 cellMatrix_10_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf475_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray475 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf475_kernel {p : ℝ × ℝ} (hp : majorizationTriangle475.Contains p) :
    (0 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 7 majorizationTriangle475
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray475
    majorizationLeaf475_polynomial_eq majorizationLeaf475_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 476. -/
def majorizationTriangle476 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 476. -/
def majorizationArray476 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2108366837105974667355409080356408874821932072109 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-121012593422537130276529702914786509441324364583 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-10274626090663079 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-2630945813964569 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-99447415191929269154006904712274292114681574183 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-549295157193317 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-431056352315099 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-2197643043420109 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (4319419018902019 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (2005675724187667 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (1069819274200297 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (2873146587860193 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (1284491357702141 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-740146311400417 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-33507792274183 /
    24000000000000000 : ℚ) else
  if p = (3, 3) then (-2548947583641437 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf476_polynomial_eq :
    lowerPullbackPolynomial 10 8 majorizationTriangle476 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray476 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 8 majorizationTriangle476
    cellMatrix_10_8 cellMatrix_10_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf476_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray476 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf476_kernel {p : ℝ × ℝ} (hp : majorizationTriangle476.Contains p) :
    (0 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 8 majorizationTriangle476
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray476
    majorizationLeaf476_polynomial_eq majorizationLeaf476_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 477. -/
def majorizationTriangle477 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 477. -/
def majorizationArray477 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (7015339738253498479642654435371639648910485151 /
    14261069252567580766837911060480000000000000000 : ℚ) else
  if p = (0, 1) then (21077006591570430451394269815915265800267590177 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (-23804944631627519 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (14608912499765459 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (7503501152375953898372909135544201070199663137 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (7111950278645473 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-5716333538406221 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (1615148716391767 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (8520521446017907 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-6137111059741 /
    8000000000000000 : ℚ) else
  if p = (2, 2) then (-1344226103639447 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (1576350570985169 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (4548274110542861 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-2522265251935063 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (3677828380473441 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-2548947583641437 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf477_polynomial_eq :
    lowerPullbackPolynomial 10 8 majorizationTriangle477 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray477 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 8 majorizationTriangle477
    cellMatrix_10_8 cellMatrix_10_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf477_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray477 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf477_kernel {p : ℝ × ℝ} (hp : majorizationTriangle477.Contains p) :
    (0 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 8 majorizationTriangle477
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray477
    majorizationLeaf477_polynomial_eq majorizationLeaf477_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 478. -/
def majorizationTriangle478 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 478. -/
def majorizationArray478 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (102829810925061007518049756257357264569523126773 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-7571302737654322050920198711003503620645703179 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 2) then (-169765692081721 /
    3000000000000000 : ℚ) else
  if p = (0, 3) then (9177783618703211 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (-4527154314818063992691679293549433177482710539 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (1, 1) then (-1451557883504223 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (-328587424466901 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (-101908539724989 /
    4000000000000000 : ℚ) else
  if p = (2, 0) then (2216534377764649 /
    60000000000000000 : ℚ) else
  if p = (2, 1) then (319118850904221 /
    5000000000000000 : ℚ) else
  if p = (2, 2) then (2422314759445219 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-1001165049324283 /
    12000000000000000 : ℚ) else
  if p = (3, 0) then (-4548274110542861 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-2522265251935063 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (-3677828380473441 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (95592125331097439 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf478_polynomial_eq :
    lowerPullbackPolynomial 10 9 majorizationTriangle478 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray478 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 9 majorizationTriangle478
    cellMatrix_10_9 cellMatrix_10_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf478_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray478 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf478_kernel {p : ℝ × ℝ} (hp : majorizationTriangle478.Contains p) :
    (0 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 9 majorizationTriangle478
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray478
    majorizationLeaf478_polynomial_eq majorizationLeaf478_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 479. -/
def majorizationTriangle479 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 479. -/
def majorizationArray479 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1177419106322211755197681901092934732387265179 /
    4456584141427368989636847206400000000000000000 : ℚ) else
  if p = (0, 1) then (5809922540812791628955303831460605869430868577 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (0, 2) then (-12706037656447973 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (3002133999351597 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (467568335077090159706537557537880755861916257 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (1, 1) then (-79127700288831 /
    12500000000000000 : ℚ) else
  if p = (1, 2) then (1409432702167299 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (-19810660560079211 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (5048199932946343 /
    60000000000000000 : ℚ) else
  if p = (2, 1) then (-33592850339139 /
    156250000000000 : ℚ) else
  if p = (2, 2) then (22094823380621921 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-15177957621627763 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-5506434398090971 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (10152304798096913 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (-21139660047419279 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (95592125331097439 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf479_polynomial_eq :
    lowerPullbackPolynomial 10 9 majorizationTriangle479 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray479 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 9 majorizationTriangle479
    cellMatrix_10_9 cellMatrix_10_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf479_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray479 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf479_kernel {p : ℝ × ℝ} (hp : majorizationTriangle479.Contains p) :
    (0 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 9 majorizationTriangle479
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray479
    majorizationLeaf479_polynomial_eq majorizationLeaf479_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 480. -/
def majorizationTriangle480 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 480. -/
def majorizationArray480 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (65212702746115984511911091447651390477593609633 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-3437011141371777802471571395583514966707079777 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (0, 2) then (2466820658330093 /
    37500000000000000 : ℚ) else
  if p = (0, 3) then (5506434398090971 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-3437011141371777802471571395583514966707079777 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (1, 1) then (-13174955642117829 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-8957490177241779 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (10152304798096913 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (2466820658330093 /
    37500000000000000 : ℚ) else
  if p = (2, 1) then (-8957490177241779 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-20184496714216637 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (21139660047419279 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (5506434398090971 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (10152304798096913 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (21139660047419279 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (-221432055732504103 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf480_polynomial_eq :
    lowerPullbackPolynomial 10 10 majorizationTriangle480 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray480 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 10 majorizationTriangle480
    cellMatrix_10_10 cellMatrix_10_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf480_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray480 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf480_kernel {p : ℝ × ℝ} (hp : majorizationTriangle480.Contains p) :
    (0 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 10 majorizationTriangle480
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray480
    majorizationLeaf480_polynomial_eq majorizationLeaf480_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 481. -/
def majorizationTriangle481 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 481. -/
def majorizationArray481 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (274850147805164768581083590249228144136795787 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (24990870555430973655445703026489711712362832581 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (175174069372661729 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-225998219998453621 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (24990870555430973655445703026489711712362832581 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-20855643812535669 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (5495273586241383 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (2866351145143869 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (175174069372661729 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (5495273586241383 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-18536753756316629 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (136873415542826987 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-225998219998453621 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (2866351145143869 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (136873415542826987 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-221432055732504103 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf481_polynomial_eq :
    lowerPullbackPolynomial 10 10 majorizationTriangle481 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray481 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 10 10 majorizationTriangle481
    cellMatrix_10_10 cellMatrix_10_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf481_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray481 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf481_kernel {p : ℝ × ℝ} (hp : majorizationTriangle481.Contains p) :
    (0 : ℝ) ≤ kernel (((10 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 10 10 majorizationTriangle481
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray481
    majorizationLeaf481_polynomial_eq majorizationLeaf481_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
