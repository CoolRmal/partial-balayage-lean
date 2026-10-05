/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices32

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

/-- The actual closed rational triangle of majorization leaf 769. -/
def majorizationTriangle769 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 769. -/
def majorizationArray769 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (69076057479797736075425571884772586374635360387 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 1) then (-32493656706996795756335440751928853246805087047 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (513751505823581 /
    40000000000000000 : ℚ) else
  if p = (0, 3) then (-4968883217507887 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-33393272560894197068108042166933623874804585287 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (3366968690632743 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (2107810049058913 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-1615066472968247 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (3136494950603247 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (1540072627573571 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-7014851367265227 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (1950448147422211 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (-869495524088323 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (-166399720278197 /
    25000000000000000 : ℚ) else
  if p = (3, 2) then (73971656456003 /
    4687500000000000 : ℚ) else
  if p = (3, 3) then (-339048927672617 /
    50000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf769_polynomial_eq :
    lowerPullbackPolynomial 22 3 majorizationTriangle769 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray769 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 22 3 majorizationTriangle769
    cellMatrix_22_3 cellMatrix_22_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf769_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray769 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf769_kernel {p : ℝ × ℝ} (hp : majorizationTriangle769.Contains p) :
    (0 : ℝ) ≤ kernel (((22 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 22 3 majorizationTriangle769
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray769
    majorizationLeaf769_polynomial_eq majorizationLeaf769_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 770. -/
def majorizationTriangle770 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 770. -/
def majorizationArray770 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (32497214358872138161475135455980843945112687 /
    792281625142643375935439503360000000000000000 : ℚ) else
  if p = (0, 1) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 3) then (2453520659103157 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 3) then (2453520659103157 /
    600000000000000000 : ℚ) else
  if p = (2, 3) then (2453520659103157 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (684347342461457 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (684347342461457 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (684347342461457 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (-339048927672617 /
    50000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf770_polynomial_eq :
    lowerPullbackPolynomial 22 3 majorizationTriangle770 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray770 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 22 3 majorizationTriangle770
    cellMatrix_22_3 cellMatrix_22_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf770_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray770 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf770_kernel {p : ℝ × ℝ} (hp : majorizationTriangle770.Contains p) :
    (0 : ℝ) ≤ kernel (((22 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 22 3 majorizationTriangle770
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray770
    majorizationLeaf770_polynomial_eq majorizationLeaf770_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 771. -/
def majorizationTriangle771 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 771. -/
def majorizationArray771 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (243089545695567926273576361456629657229075155377 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-44924902399328941721788750322660905947673803499 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (684347342461457 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-684347342461457 /
    450000000000000000 : ℚ) else
  if p = (1, 0) then (-44924902399328941721788750322660905947673803499 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (684347342461457 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (-684347342461457 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (684347342461457 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (684347342461457 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-684347342461457 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (684347342461457 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-684347342461457 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (-684347342461457 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (684347342461457 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (-684347342461457 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (684347342461457 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf771_polynomial_eq :
    lowerPullbackPolynomial 22 4 majorizationTriangle771 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray771 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 22 4 majorizationTriangle771
    cellMatrix_22_4 cellMatrix_22_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf771_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray771 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf771_kernel {p : ℝ × ℝ} (hp : majorizationTriangle771.Contains p) :
    (0 : ℝ) ≤ kernel (((22 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 22 4 majorizationTriangle771
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray771
    majorizationLeaf771_polynomial_eq majorizationLeaf771_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 772. -/
def majorizationTriangle772 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 772. -/
def majorizationArray772 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 3) then (684347342461457 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf772_polynomial_eq :
    lowerPullbackPolynomial 22 4 majorizationTriangle772 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray772 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 22 4 majorizationTriangle772
    cellMatrix_22_4 cellMatrix_22_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf772_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray772 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf772_kernel {p : ℝ × ℝ} (hp : majorizationTriangle772.Contains p) :
    (0 : ℝ) ≤ kernel (((22 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 22 4 majorizationTriangle772
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray772
    majorizationLeaf772_polynomial_eq majorizationLeaf772_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 773. -/
def majorizationTriangle773 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 773. -/
def majorizationArray773 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf773_polynomial_eq :
    lowerPullbackPolynomial 22 5 majorizationTriangle773 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray773 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 22 5 majorizationTriangle773
    cellMatrix_22_5 cellMatrix_22_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf773_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray773 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf773_kernel {p : ℝ × ℝ} (hp : majorizationTriangle773.Contains p) :
    (0 : ℝ) ≤ kernel (((22 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 22 5 majorizationTriangle773
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray773
    majorizationLeaf773_polynomial_eq majorizationLeaf773_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 774. -/
def majorizationTriangle774 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 774. -/
def majorizationArray774 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (22662493018738128556002774075266595326753015311 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (0, 2) then (-379209169895277 /
    50000000000000000 : ℚ) else
  if p = (0, 3) then (-592098697059311 /
    450000000000000000 : ℚ) else
  if p = (1, 0) then (-5829257208991061419714711144294782249455331361 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (1, 2) then (-199961724343017 /
    12500000000000000 : ℚ) else
  if p = (1, 3) then (2618897801183759 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (43651041377671 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-1146854233685973 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (1352516749761161 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (-1345022277868909 /
    900000000000000000 : ℚ) else
  if p = (3, 2) then (3092017577410657 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (-3084996933436459 /
    225000000000000000 : ℚ) else
  if p = (0, 1) then (-4382731326445484416980866696021107770663118881 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf774_polynomial_eq :
    lowerPullbackPolynomial 23 0 majorizationTriangle774 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray774 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 23 0 majorizationTriangle774
    cellMatrix_23_0 cellMatrix_23_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf774_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray774 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf774_kernel {p : ℝ × ℝ} (hp : majorizationTriangle774.Contains p) :
    (0 : ℝ) ≤ kernel (((23 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 23 0 majorizationTriangle774
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray774
    majorizationLeaf774_polynomial_eq majorizationLeaf774_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 775. -/
def majorizationTriangle775 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 775. -/
def majorizationArray775 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1715470331775573997640218524551353496638600783 /
    11884224377139650639031592550400000000000000000 : ℚ) else
  if p = (0, 1) then (63858095391336614959050045630600145224470921689 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (930427540640719 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (-10562709272820751 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (65412462257788478957270748876492904273039098329 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (1092892916193783 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-1095968490860497 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (1099044065527211 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (146957923912959 /
    12500000000000000 : ℚ) else
  if p = (2, 1) then (-106341580024693 /
    12500000000000000 : ℚ) else
  if p = (2, 2) then (-189974627953239 /
    6250000000000000 : ℚ) else
  if p = (2, 3) then (866240091837649 /
    37500000000000000 : ℚ) else
  if p = (3, 0) then (-4867095452849197 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (1170107329033 /
    12500000000000000 : ℚ) else
  if p = (3, 2) then (3077976289462261 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (-3084996933436459 /
    225000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf775_polynomial_eq :
    lowerPullbackPolynomial 23 0 majorizationTriangle775 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray775 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 23 0 majorizationTriangle775
    cellMatrix_23_0 cellMatrix_23_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf775_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray775 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf775_kernel {p : ℝ × ℝ} (hp : majorizationTriangle775.Contains p) :
    (0 : ℝ) ≤ kernel (((23 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 23 0 majorizationTriangle775
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray775
    majorizationLeaf775_polynomial_eq majorizationLeaf775_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 776. -/
def majorizationTriangle776 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 776. -/
def majorizationArray776 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (626058259301252519649611930307143233488238440347 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-66249402270950918382088807763148811757514162649 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-864863103372571 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (4553181338076547 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-72342977132144385712702825827600902405404000729 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-580489788304513 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (1019204006439623 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-23601571911199 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1340105278938181 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (51415629018797 /
    6250000000000000 : ℚ) else
  if p = (2, 2) then (1558179265836349 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-4208415439474001 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (4867095452849197 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (1170107329033 /
    12500000000000000 : ℚ) else
  if p = (3, 2) then (-3077976289462261 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (20893295819979931 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf776_polynomial_eq :
    lowerPullbackPolynomial 23 1 majorizationTriangle776 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray776 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 23 1 majorizationTriangle776
    cellMatrix_23_1 cellMatrix_23_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf776_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray776 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf776_kernel {p : ℝ × ℝ} (hp : majorizationTriangle776.Contains p) :
    (0 : ℝ) ≤ kernel (((23 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 23 1 majorizationTriangle776
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray776
    majorizationLeaf776_polynomial_eq majorizationLeaf776_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 777. -/
def majorizationTriangle777 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 777. -/
def majorizationArray777 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (6184623666489870398744194909499152930987758281 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (23784746613309671114221527882161463946140521287 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (54721535176357 /
    15000000000000000 : ℚ) else
  if p = (0, 3) then (1696851918395017 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (23784746613309671114221527882161463946140521287 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (54721535176357 /
    5000000000000000 : ℚ) else
  if p = (1, 2) then (54721535176357 /
    5000000000000000 : ℚ) else
  if p = (1, 3) then (-730133064795879 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (54721535176357 /
    15000000000000000 : ℚ) else
  if p = (2, 1) then (54721535176357 /
    5000000000000000 : ℚ) else
  if p = (2, 2) then (54721535176357 /
    5000000000000000 : ℚ) else
  if p = (2, 3) then (-1033506187694741 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (409315552832537 /
    120000000000000000 : ℚ) else
  if p = (3, 1) then (-3674349343924573 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-2860463554043629 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (20893295819979931 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf777_polynomial_eq :
    lowerPullbackPolynomial 23 1 majorizationTriangle777 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray777 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 23 1 majorizationTriangle777
    cellMatrix_23_1 cellMatrix_23_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf777_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray777 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf777_kernel {p : ℝ × ℝ} (hp : majorizationTriangle777.Contains p) :
    (0 : ℝ) ≤ kernel (((23 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 23 1 majorizationTriangle777
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray777
    majorizationLeaf777_polynomial_eq majorizationLeaf777_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 778. -/
def majorizationTriangle778 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 778. -/
def majorizationArray778 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (205113695059020184116707620415542138697396236681 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-10426265060173724319512982309386001149431580269 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (6740639187249073 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-119086625781831 /
    50000000000000000 : ℚ) else
  if p = (1, 0) then (-10705844609936818637072882575434141900532549229 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (2892234877238267 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (2014806440968047 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-1117081775017801 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (1665718939908467 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (1485487936870293 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-6392529255076607 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (737170826181647 /
    50000000000000000 : ℚ) else
  if p = (3, 0) then (-409315552832537 /
    120000000000000000 : ℚ) else
  if p = (3, 1) then (-3674349343924573 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (2860463554043629 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-2758727830308511 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf778_polynomial_eq :
    lowerPullbackPolynomial 23 2 majorizationTriangle778 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray778 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 23 2 majorizationTriangle778
    cellMatrix_23_2 cellMatrix_23_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf778_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray778 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf778_kernel {p : ℝ × ℝ} (hp : majorizationTriangle778.Contains p) :
    (0 : ℝ) ≤ kernel (((23 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 23 2 majorizationTriangle778
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray778
    majorizationLeaf778_polynomial_eq majorizationLeaf778_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 779. -/
def majorizationTriangle779 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 779. -/
def majorizationArray779 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (32497214358872138161475135455980843945112687 /
    792281625142643375935439503360000000000000000 : ℚ) else
  if p = (0, 1) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 3) then (54721535176357 /
    45000000000000000 : ℚ) else
  if p = (1, 0) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 3) then (54721535176357 /
    15000000000000000 : ℚ) else
  if p = (2, 3) then (54721535176357 /
    15000000000000000 : ℚ) else
  if p = (3, 0) then (2453520659103157 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (2453520659103157 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (2453520659103157 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-2758727830308511 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf779_polynomial_eq :
    lowerPullbackPolynomial 23 2 majorizationTriangle779 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray779 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 23 2 majorizationTriangle779
    cellMatrix_23_2 cellMatrix_23_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf779_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray779 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf779_kernel {p : ℝ × ℝ} (hp : majorizationTriangle779.Contains p) :
    (0 : ℝ) ≤ kernel (((23 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 23 2 majorizationTriangle779
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray779
    majorizationLeaf779_polynomial_eq majorizationLeaf779_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
