/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices0

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

/-- The actual closed rational triangle of majorization leaf 0. -/
def majorizationTriangle0 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 0. -/
def majorizationArray0 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (4768076816976185873290508116697109047727186691489 /
    57044277010270323067351644241920000000000000000 : ℚ) else
  if p = (0, 2) then (4272954493350132607 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-12484546856254210157 /
    900000000000000000 : ℚ) else
  if p = (2, 0) then (4272954493350132607 /
    150000000000000000 : ℚ) else
  if p = (2, 2) then (-340992498652911263 /
    5000000000000000 : ℚ) else
  if p = (2, 3) then (549436948932703163 /
    15000000000000000 : ℚ) else
  if p = (3, 0) then (-12484546856254210157 /
    900000000000000000 : ℚ) else
  if p = (3, 2) then (549436948932703163 /
    15000000000000000 : ℚ) else
  if p = (3, 3) then (-18011598276544751507 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-1906643824431262624916613107470110939381491072661 /
    31691265005705735037417580134400000000000000000 : ℚ) else
  if p = (0, 1) then (-1906643824431262624916613107470110939381491072661 /
    31691265005705735037417580134400000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf0_polynomial_eq :
    lowerPullbackPolynomial 0 0 majorizationTriangle0 radialPowerData0.radius
      (certifiedRadialHeight radialPowerData0 radialPowerData32)
      (certifiedRadialSlope radialPowerData0) 1 =
        planeArrayPolynomial majorizationArray0 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 0 0 majorizationTriangle0
    cellMatrix_0_0 cellMatrix_0_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf0_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray0 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf0_kernel {p : ℝ × ℝ} (hp : majorizationTriangle0.Contains p) :
    (1 : ℝ) ≤ kernel (((0 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 0 0 majorizationTriangle0
    radialPowerData0 radialPowerData32 radialPowerData0_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray0
    majorizationLeaf0_polynomial_eq majorizationLeaf0_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 1. -/
def majorizationTriangle1 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 1. -/
def majorizationArray1 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (334623714506750292489944200206728529553677394129 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (1310377061259280000557873700335393044000132965841 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (154516984934288081 /
    30000000000000000 : ℚ) else
  if p = (0, 3) then (-617517950790807029 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (1310377061259280000557873700335393044000132965841 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (2, 0) then (154516984934288081 /
    30000000000000000 : ℚ) else
  if p = (1, 1) then (-1336042254161399507 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-1314918713300987753 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (-1314918713300987753 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-2853970292294850247 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (1321959893587791671 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (7022859297890688247 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-617517950790807029 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (1321959893587791671 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (7022859297890688247 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-18011598276544751507 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf1_polynomial_eq :
    lowerPullbackPolynomial 0 0 majorizationTriangle1 radialPowerData1.radius
      (certifiedRadialHeight radialPowerData1 radialPowerData32)
      (certifiedRadialSlope radialPowerData1) 1 =
        planeArrayPolynomial majorizationArray1 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 0 0 majorizationTriangle1
    cellMatrix_0_0 cellMatrix_0_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf1_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray1 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf1_kernel {p : ℝ × ℝ} (hp : majorizationTriangle1.Contains p) :
    (1 : ℝ) ≤ kernel (((0 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 0 0 majorizationTriangle1
    radialPowerData1 radialPowerData32 radialPowerData1_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray1
    majorizationLeaf1_polynomial_eq majorizationLeaf1_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 55. -/
def majorizationTriangle55 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 55. -/
def majorizationArray55 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (903909621852104281246996337960172231166841154037 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 2) then (-154150325636724551 /
    50000000000000000 : ℚ) else
  if p = (0, 3) then (617517950790807029 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (269037634679244258347199606292453821542377052719 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 2) then (-132548048373119363 /
    5000000000000000 : ℚ) else
  if p = (1, 3) then (1321959893587791671 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-1312879289851314981 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (2084444502797919 /
    50000000000000 : ℚ) else
  if p = (2, 3) then (-7022859297890688247 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (767681114920918547 /
    180000000000000000 : ℚ) else
  if p = (3, 2) then (-4887572231561790947 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (3424534258294901099 /
    360000000000000000 : ℚ) else
  if p = (0, 1) then (-518696829801160029397252676728278866111831084187 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf55_polynomial_eq :
    lowerPullbackPolynomial 1 0 majorizationTriangle55 radialPowerData1.radius
      (certifiedRadialHeight radialPowerData1 radialPowerData32)
      (certifiedRadialSlope radialPowerData1) 1 =
        planeArrayPolynomial majorizationArray55 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 1 0 majorizationTriangle55
    cellMatrix_1_0 cellMatrix_1_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf55_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray55 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf55_kernel {p : ℝ × ℝ} (hp : majorizationTriangle55.Contains p) :
    (1 : ℝ) ≤ kernel (((1 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 1 0 majorizationTriangle55
    radialPowerData1 radialPowerData32 radialPowerData1_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray55
    majorizationLeaf55_polynomial_eq majorizationLeaf55_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 56. -/
def majorizationTriangle56 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 56. -/
def majorizationArray56 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (405145412497376216992718246683897302932790737921 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (1197273875863276832325633332282988699159204777887 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (1203557053073510257 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-3720937195037082323 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (85679692834596161144880826949186115794945757087 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (31994542021698741 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (1438516914226501881 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-1012335512853832489 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-1435611250001293097 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-202219791829317213 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (1639586243761223107 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-3076952695693129001 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (1508650316229018239 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-2427617634772658293 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-2449175609450307867 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (3424534258294901099 /
    360000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf56_polynomial_eq :
    lowerPullbackPolynomial 1 0 majorizationTriangle56 radialPowerData2.radius
      (certifiedRadialHeight radialPowerData2 radialPowerData32)
      (certifiedRadialSlope radialPowerData2) 1 =
        planeArrayPolynomial majorizationArray56 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 1 0 majorizationTriangle56
    cellMatrix_1_0 cellMatrix_1_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf56_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray56 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf56_kernel {p : ℝ × ℝ} (hp : majorizationTriangle56.Contains p) :
    (1 : ℝ) ≤ kernel (((1 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 1 0 majorizationTriangle56
    radialPowerData2 radialPowerData32 radialPowerData2_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray56
    majorizationLeaf56_polynomial_eq majorizationLeaf56_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 57. -/
def majorizationTriangle57 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 57. -/
def majorizationArray57 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (9047628015728299493775324208216147917295523003563 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-1568050022997284369275197614282605952885510008541 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (154516984934288081 /
    30000000000000000 : ℚ) else
  if p = (0, 3) then (-1508650316229018239 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-1568050022997284369275197614282605952885510008541 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-1336042254161399507 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (1314918713300987753 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-2427617634772658293 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (154516984934288081 /
    30000000000000000 : ℚ) else
  if p = (2, 1) then (1314918713300987753 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-2853970292294850247 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (2449175609450307867 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-1508650316229018239 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-2427617634772658293 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (2449175609450307867 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-10365732014613475897 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf57_polynomial_eq :
    lowerPullbackPolynomial 1 1 majorizationTriangle57 radialPowerData2.radius
      (certifiedRadialHeight radialPowerData2 radialPowerData32)
      (certifiedRadialSlope radialPowerData2) 1 =
        planeArrayPolynomial majorizationArray57 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 1 1 majorizationTriangle57
    cellMatrix_1_1 cellMatrix_1_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf57_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray57 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf57_kernel {p : ℝ × ℝ} (hp : majorizationTriangle57.Contains p) :
    (1 : ℝ) ≤ kernel (((1 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 1 1 majorizationTriangle57
    radialPowerData2 radialPowerData32 radialPowerData2_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray57
    majorizationLeaf57_polynomial_eq majorizationLeaf57_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 58. -/
def majorizationTriangle58 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 58. -/
def majorizationArray58 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (11950298149619317169162535157894194562776929819 /
    7922816251426433759354395033600000000000000000 : ℚ) else
  if p = (0, 1) then (1186013786258487170689496535978380511605816883103 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (357200556835925189 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (13195538256573469 /
    180000000000000000 : ℚ) else
  if p = (1, 0) then (1186013786258487170689496535978380511605816883103 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-163071422205759409 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-463187093089211131 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (475426001828928253 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (357200556835925189 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-463187093089211131 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-1378618942501329189 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (377275648282819037 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (13195538256573469 /
    180000000000000000 : ℚ) else
  if p = (3, 1) then (475426001828928253 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (377275648282819037 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (-10365732014613475897 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf58_polynomial_eq :
    lowerPullbackPolynomial 1 1 majorizationTriangle58 radialPowerData3.radius
      (certifiedRadialHeight radialPowerData3 radialPowerData32)
      (certifiedRadialSlope radialPowerData3) 1 =
        planeArrayPolynomial majorizationArray58 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 1 1 majorizationTriangle58
    cellMatrix_1_1 cellMatrix_1_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf58_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray58 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf58_kernel {p : ℝ × ℝ} (hp : majorizationTriangle58.Contains p) :
    (1 : ℝ) ≤ kernel (((1 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 1 1 majorizationTriangle58
    radialPowerData3 radialPowerData32 radialPowerData3_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray58
    majorizationLeaf58_polynomial_eq majorizationLeaf58_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 108. -/
def majorizationTriangle108 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 108. -/
def majorizationArray108 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (18791011378662241445670341924204365395217940544683 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 2) then (-1258690070981786033 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (3720937195037082323 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-550078824862934217806184515967079772247785263007 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 2) then (799244812167497793 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-1012335512853832489 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-6264518434334513 /
    18750000000000000 : ℚ) else
  if p = (2, 2) then (-718683225965952947 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (3076952695693129001 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-4165196011383343 /
    225000000000000000 : ℚ) else
  if p = (3, 2) then (709547602477051157 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-3180455862888220331 /
    1800000000000000000 : ℚ) else
  if p = (0, 1) then (-850301245191361573270244977893460056742317051807 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf108_polynomial_eq :
    lowerPullbackPolynomial 2 0 majorizationTriangle108 radialPowerData2.radius
      (certifiedRadialHeight radialPowerData2 radialPowerData32)
      (certifiedRadialSlope radialPowerData2) 1 =
        planeArrayPolynomial majorizationArray108 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 2 0 majorizationTriangle108
    cellMatrix_2_0 cellMatrix_2_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf108_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray108 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf108_kernel {p : ℝ × ℝ} (hp : majorizationTriangle108.Contains p) :
    (1 : ℝ) ≤ kernel (((2 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 2 0 majorizationTriangle108
    radialPowerData2 radialPowerData32 radialPowerData2_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray108
    majorizationLeaf108_polynomial_eq majorizationLeaf108_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 109. -/
def majorizationTriangle109 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 109. -/
def majorizationArray109 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (113563430705940287321743501283933369784708809297 /
    23768448754279301278063185100800000000000000000 : ℚ) else
  if p = (0, 1) then (1203912387515713439505965745487809957064320679221 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (7567397290592653 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (-110053300590626099 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (1017710527382659778597888373578661659620718213023 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (55536710196778107 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (-19823728840456579 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (-15889252515864949 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-13070102203942441 /
    20000000000000000 : ℚ) else
  if p = (2, 1) then (14004566115069849 /
    20000000000000000 : ℚ) else
  if p = (2, 2) then (-12177441417289491 /
    20000000000000000 : ℚ) else
  if p = (2, 3) then (3450105573169711 /
    20000000000000000 : ℚ) else
  if p = (3, 0) then (-1043508183883019867 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-114088484326671901 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (1761360657934118017 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-3180455862888220331 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf109_polynomial_eq :
    lowerPullbackPolynomial 2 0 majorizationTriangle109 radialPowerData3.radius
      (certifiedRadialHeight radialPowerData3 radialPowerData32)
      (certifiedRadialSlope radialPowerData3) 1 =
        planeArrayPolynomial majorizationArray109 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 2 0 majorizationTriangle109
    cellMatrix_2_0 cellMatrix_2_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf109_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray109 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf109_kernel {p : ℝ × ℝ} (hp : majorizationTriangle109.Contains p) :
    (1 : ℝ) ≤ kernel (((2 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 2 0 majorizationTriangle109
    radialPowerData3 radialPowerData32 radialPowerData3_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray109
    majorizationLeaf109_polynomial_eq majorizationLeaf109_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 110. -/
def majorizationTriangle110 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 110. -/
def majorizationArray110 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (13163302220622246002259254311389099761828326931669 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-1597048896070457905795688207477503858397117873461 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (1203557053073510257 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-13195538256573469 /
    180000000000000000 : ℚ) else
  if p = (1, 0) then (626139469986903436565816803190101308331400168139 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (31994542021698741 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-1438516914226501881 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (475426001828928253 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-1435611250001293097 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (202219791829317213 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (1639586243761223107 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-377275648282819037 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (1043508183883019867 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-114088484326671901 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-1761360657934118017 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (3652589925543997369 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf110_polynomial_eq :
    lowerPullbackPolynomial 2 1 majorizationTriangle110 radialPowerData3.radius
      (certifiedRadialHeight radialPowerData3 radialPowerData32)
      (certifiedRadialSlope radialPowerData3) 1 =
        planeArrayPolynomial majorizationArray110 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 2 1 majorizationTriangle110
    cellMatrix_2_1 cellMatrix_2_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf110_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray110 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf110_kernel {p : ℝ × ℝ} (hp : majorizationTriangle110.Contains p) :
    (1 : ℝ) ≤ kernel (((2 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 2 1 majorizationTriangle110
    radialPowerData3 radialPowerData32 radialPowerData3_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray110
    majorizationLeaf110_polynomial_eq majorizationLeaf110_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 111. -/
def majorizationTriangle111 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 111. -/
def majorizationArray111 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (42022334767790068857039702831214803221255000087 /
    23768448754279301278063185100800000000000000000 : ℚ) else
  if p = (0, 1) then (11175219391055197311469268140122805059016842259 /
    4951760157141521099596496896000000000000000000 : ℚ) else
  if p = (0, 2) then (14435692658753383 /
    40000000000000000 : ℚ) else
  if p = (0, 3) then (-19014556237527203 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-10974077610014402449981783794482250489106426823 /
    14855280471424563298789490688000000000000000000 : ℚ) else
  if p = (1, 1) then (-101379768154629151 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (80564304860713579 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-160705479888464737 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-181059517602536119 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-250790249784956763 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (512610325108550163 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-211461579760481691 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (44855006203205109 /
    50000000000000000 : ℚ) else
  if p = (3, 1) then (-6637401353257949 /
    18750000000000000 : ℚ) else
  if p = (3, 2) then (-78801219483744973 /
    25000000000000000 : ℚ) else
  if p = (3, 3) then (3652589925543997369 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf111_polynomial_eq :
    lowerPullbackPolynomial 2 1 majorizationTriangle111 radialPowerData4.radius
      (certifiedRadialHeight radialPowerData4 radialPowerData32)
      (certifiedRadialSlope radialPowerData4) 1 =
        planeArrayPolynomial majorizationArray111 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 2 1 majorizationTriangle111
    cellMatrix_2_1 cellMatrix_2_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf111_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray111 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf111_kernel {p : ℝ × ℝ} (hp : majorizationTriangle111.Contains p) :
    (1 : ℝ) ≤ kernel (((2 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 2 1 majorizationTriangle111
    radialPowerData4 radialPowerData32 radialPowerData4_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray111
    majorizationLeaf111_polynomial_eq majorizationLeaf111_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 112. -/
def majorizationTriangle112 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 112. -/
def majorizationArray112 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (40448282649983644711388481691440987959193729897 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 1) then (-2109045091686559966943159883146530458123473977 /
    14855280471424563298789490688000000000000000000 : ℚ) else
  if p = (0, 2) then (357200556835925189 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-44855006203205109 /
    50000000000000000 : ℚ) else
  if p = (1, 0) then (-2109045091686559966943159883146530458123473977 /
    14855280471424563298789490688000000000000000000 : ℚ) else
  if p = (1, 1) then (-163071422205759409 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (463187093089211131 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-6637401353257949 /
    18750000000000000 : ℚ) else
  if p = (2, 0) then (357200556835925189 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (463187093089211131 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-1378618942501329189 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (78801219483744973 /
    25000000000000000 : ℚ) else
  if p = (3, 0) then (-44855006203205109 /
    50000000000000000 : ℚ) else
  if p = (3, 1) then (-6637401353257949 /
    18750000000000000 : ℚ) else
  if p = (3, 2) then (78801219483744973 /
    25000000000000000 : ℚ) else
  if p = (3, 3) then (-499673741115283741 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf112_polynomial_eq :
    lowerPullbackPolynomial 2 2 majorizationTriangle112 radialPowerData4.radius
      (certifiedRadialHeight radialPowerData4 radialPowerData32)
      (certifiedRadialSlope radialPowerData4) 1 =
        planeArrayPolynomial majorizationArray112 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 2 2 majorizationTriangle112
    cellMatrix_2_2 cellMatrix_2_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf112_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray112 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf112_kernel {p : ℝ × ℝ} (hp : majorizationTriangle112.Contains p) :
    (1 : ℝ) ≤ kernel (((2 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 2 2 majorizationTriangle112
    radialPowerData4 radialPowerData32 radialPowerData4_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray112
    majorizationLeaf112_polynomial_eq majorizationLeaf112_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 113. -/
def majorizationTriangle113 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 113. -/
def majorizationArray113 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2013321942835440471958379320932473410726417711 /
    4753689750855860255612637020160000000000000000 : ℚ) else
  if p = (0, 1) then (16009614201206148351474515921799385697423392429 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (0, 2) then (213403330930363109 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-23537477939432699 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (16009614201206148351474515921799385697423392429 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (1, 1) then (-335003571537963051 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-33839544184046799 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (57201924522380189 /
    60000000000000000 : ℚ) else
  if p = (2, 0) then (213403330930363109 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-33839544184046799 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (-594202853973272931 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (184468863180303849 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-23537477939432699 /
    100000000000000000 : ℚ) else
  if p = (3, 1) then (57201924522380189 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (184468863180303849 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-499673741115283741 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf113_polynomial_eq :
    lowerPullbackPolynomial 2 2 majorizationTriangle113 radialPowerData5.radius
      (certifiedRadialHeight radialPowerData5 radialPowerData32)
      (certifiedRadialSlope radialPowerData5) 1 =
        planeArrayPolynomial majorizationArray113 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 2 2 majorizationTriangle113
    cellMatrix_2_2 cellMatrix_2_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf113_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray113 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf113_kernel {p : ℝ × ℝ} (hp : majorizationTriangle113.Contains p) :
    (1 : ℝ) ≤ kernel (((2 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 2 2 majorizationTriangle113
    radialPowerData5 radialPowerData32 radialPowerData5_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray113
    majorizationLeaf113_polynomial_eq majorizationLeaf113_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
