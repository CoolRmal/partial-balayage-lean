/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices30

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

/-- The actual closed rational triangle of majorization leaf 747. -/
def majorizationTriangle747 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 747. -/
def majorizationArray747 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (244104463731544444380433113406780072347449166257 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-45939820435305459828645502272811321066047814379 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (1688946349157141 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-1688946349157141 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-45939820435305459828645502272811321066047814379 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (1688946349157141 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-1688946349157141 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (1688946349157141 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (1688946349157141 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-1688946349157141 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (1688946349157141 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-1688946349157141 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-1688946349157141 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (1688946349157141 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-1688946349157141 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (1688946349157141 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf747_polynomial_eq :
    lowerPullbackPolynomial 20 6 majorizationTriangle747 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray747 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 6 majorizationTriangle747
    cellMatrix_20_6 cellMatrix_20_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf747_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray747 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf747_kernel {p : ℝ × ℝ} (hp : majorizationTriangle747.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 6 majorizationTriangle747
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray747
    majorizationLeaf747_polynomial_eq majorizationLeaf747_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 748. -/
def majorizationTriangle748 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 748. -/
def majorizationArray748 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 3) then (1688946349157141 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf748_polynomial_eq :
    lowerPullbackPolynomial 20 6 majorizationTriangle748 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray748 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 6 majorizationTriangle748
    cellMatrix_20_6 cellMatrix_20_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf748_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray748 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf748_kernel {p : ℝ × ℝ} (hp : majorizationTriangle748.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 6 majorizationTriangle748
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray748
    majorizationLeaf748_polynomial_eq majorizationLeaf748_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 749. -/
def majorizationTriangle749 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 749. -/
def majorizationArray749 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf749_polynomial_eq :
    lowerPullbackPolynomial 20 7 majorizationTriangle749 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray749 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 7 majorizationTriangle749
    cellMatrix_20_7 cellMatrix_20_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf749_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray749 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf749_kernel {p : ℝ × ℝ} (hp : majorizationTriangle749.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 7 majorizationTriangle749
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray749
    majorizationLeaf749_polynomial_eq majorizationLeaf749_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 750. -/
def majorizationTriangle750 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 750. -/
def majorizationArray750 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1291143471019365612188390023867961094041777950669 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 2) then (-768478921278107 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-27917734724323 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-77195342827574568487074919068955339455011252303 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 2) then (-261532654520387 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (41854860977591 /
    50000000000000000 : ℚ) else
  if p = (2, 0) then (-202086648874223 /
    300000000000000000 : ℚ) else
  if p = (2, 2) then (-255256842521939 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (526886718773537 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-184999459766167 /
    450000000000000000 : ℚ) else
  if p = (3, 2) then (860658927357007 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-770493086674507 /
    300000000000000000 : ℚ) else
  if p = (0, 1) then (-21229495482075468157037175910209041540795605701 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf750_polynomial_eq :
    lowerPullbackPolynomial 21 0 majorizationTriangle750 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray750 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 21 0 majorizationTriangle750
    cellMatrix_21_0 cellMatrix_21_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf750_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray750 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf750_kernel {p : ℝ × ℝ} (hp : majorizationTriangle750.Contains p) :
    (0 : ℝ) ≤ kernel (((21 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 21 0 majorizationTriangle750
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray750
    majorizationLeaf750_polynomial_eq majorizationLeaf750_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 751. -/
def majorizationTriangle751 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 751. -/
def majorizationArray751 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5378929899200884686231154467889050822424520323 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (22338106688905338890607745015862493469061707167 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-1463537825878673 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (1069868166119 /
    180000000000000000 : ℚ) else
  if p = (1, 0) then (76062801115028901903825648591084045331886858461 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-829351481025417 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (917964068818159 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-1006576656610901 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-540471855151337 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (71723546447481 /
    12500000000000000 : ℚ) else
  if p = (2, 2) then (-294797614103729 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (27884258457031 /
    4687500000000000 : ℚ) else
  if p = (3, 0) then (49750698742417 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (-590161405309507 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (725410166333257 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (-770493086674507 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf751_polynomial_eq :
    lowerPullbackPolynomial 21 0 majorizationTriangle751 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray751 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 21 0 majorizationTriangle751
    cellMatrix_21_0 cellMatrix_21_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf751_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray751 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf751_kernel {p : ℝ × ℝ} (hp : majorizationTriangle751.Contains p) :
    (0 : ℝ) ≤ kernel (((21 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 21 0 majorizationTriangle751
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray751
    majorizationLeaf751_polynomial_eq majorizationLeaf751_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 752. -/
def majorizationTriangle752 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 752. -/
def majorizationArray752 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (361331349565307773865119588296241409790970696061 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 1) then (-62714288449399175182601139858195816142768005341 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-26546555200081 /
    10000000000000000 : ℚ) else
  if p = (0, 3) then (-770599064911271 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-72952486272696610507920759121128805284895088861 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-67984035793807 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (-10403488654841 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-813474158551927 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-146990152555501 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (16373033729659 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (135814938125799 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-637262603218333 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (-49750698742417 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (-590161405309507 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-725410166333257 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (10937872151117327 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf752_polynomial_eq :
    lowerPullbackPolynomial 21 1 majorizationTriangle752 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray752 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 21 1 majorizationTriangle752
    cellMatrix_21_1 cellMatrix_21_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf752_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray752 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf752_kernel {p : ℝ × ℝ} (hp : majorizationTriangle752.Contains p) :
    (0 : ℝ) ≤ kernel (((21 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 21 1 majorizationTriangle752
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray752
    majorizationLeaf752_polynomial_eq majorizationLeaf752_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 753. -/
def majorizationTriangle753 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 753. -/
def majorizationArray753 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5405239189529531376799951407782582832028405601 /
    23768448754279301278063185100800000000000000000 : ℚ) else
  if p = (0, 1) then (19022536811775656297131287098254211313915951203 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-2019465940131373 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (3131322168636773 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (20209371191945007053477948702794364624656431203 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-1117736229056661 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-2376894870630491 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (4212823008266809 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1069998313342421 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-504896633884927 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (6030440825414163 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-1677764347648799 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (1507021071708467 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (3954268009832257 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-8036231485784299 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (10937872151117327 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf753_polynomial_eq :
    lowerPullbackPolynomial 21 1 majorizationTriangle753 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray753 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 21 1 majorizationTriangle753
    cellMatrix_21_1 cellMatrix_21_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf753_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray753 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf753_kernel {p : ℝ × ℝ} (hp : majorizationTriangle753.Contains p) :
    (0 : ℝ) ≤ kernel (((21 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 21 1 majorizationTriangle753
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray753
    majorizationLeaf753_polynomial_eq majorizationLeaf753_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 754. -/
def majorizationTriangle754 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 754. -/
def majorizationArray754 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (219567451801952965648193682049544891665044780679 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 1) then (-16260488498083156346133715249476557653676161123 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-1566995720913701 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-512925069208183 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (-6087714578689747077233671213296199299223267361 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (1, 1) then (-1106217279036837 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-51492352950423 /
    6250000000000000 : ℚ) else
  if p = (1, 3) then (2167549136730349 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-425743467079699 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-714892420203811 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-250723832546267 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (1406851516274519 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-1507021071708467 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (3954268009832257 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (8036231485784299 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-895266720430271 /
    75000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf754_polynomial_eq :
    lowerPullbackPolynomial 21 2 majorizationTriangle754 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray754 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 21 2 majorizationTriangle754
    cellMatrix_21_2 cellMatrix_21_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf754_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray754 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf754_kernel {p : ℝ × ℝ} (hp : majorizationTriangle754.Contains p) :
    (0 : ℝ) ≤ kernel (((21 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 21 2 majorizationTriangle754
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray754
    majorizationLeaf754_polynomial_eq majorizationLeaf754_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 755. -/
def majorizationTriangle755 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 755. -/
def majorizationArray755 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (70048848624430633441846122103816334303172263 /
    475368975085586025561263702016000000000000000 : ℚ) else
  if p = (0, 1) then (68961598505409287647569727934874926087635501529 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (513751505823581 /
    40000000000000000 : ℚ) else
  if p = (0, 3) then (-2294111734624639 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (70760830213204090271114930764884467343634498009 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (3366968690632743 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-2107810049058913 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-134542410785789 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (3136494950603247 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-1540072627573571 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-7014851367265227 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (434843073089313 /
    20000000000000000 : ℚ) else
  if p = (3, 0) then (-12978076124814697 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-486556769641883 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (2690033960908441 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (-895266720430271 /
    75000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf755_polynomial_eq :
    lowerPullbackPolynomial 21 2 majorizationTriangle755 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray755 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 21 2 majorizationTriangle755
    cellMatrix_21_2 cellMatrix_21_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf755_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray755 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf755_kernel {p : ℝ × ℝ} (hp : majorizationTriangle755.Contains p) :
    (0 : ℝ) ≤ kernel (((21 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 21 2 majorizationTriangle755
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray755
    majorizationLeaf755_polynomial_eq majorizationLeaf755_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 756. -/
def majorizationTriangle756 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 756. -/
def majorizationArray756 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (656740771600291255207462756393254124692020686747 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-75333155667196439969929260190546148924021047769 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-12423083714153 /
    1200000000000000 : ℚ) else
  if p = (0, 3) then (14868134987422259 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-80016095527005461063386871939054739549217653209 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-73302929590003 /
    12500000000000000 : ℚ) else
  if p = (1, 2) then (1343671489523581 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-394378630009609 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-892147818251239 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (149987146824961 /
    10000000000000000 : ℚ) else
  if p = (2, 2) then (3217659218638489 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-14203061526006187 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (12978076124814697 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-486556769641883 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-2690033960908441 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (3992550377186207 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf756_polynomial_eq :
    lowerPullbackPolynomial 21 3 majorizationTriangle756 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray756 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 21 3 majorizationTriangle756
    cellMatrix_21_3 cellMatrix_21_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf756_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray756 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf756_kernel {p : ℝ × ℝ} (hp : majorizationTriangle756.Contains p) :
    (0 : ℝ) ≤ kernel (((21 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 21 3 majorizationTriangle756
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray756
    majorizationLeaf756_polynomial_eq majorizationLeaf756_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 757. -/
def majorizationTriangle757 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 757. -/
def majorizationArray757 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1241270619555940790409969737432703568400807669 /
    14261069252567580766837911060480000000000000000 : ℚ) else
  if p = (0, 1) then (24219335239106342180334603435448762166466122567 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (684347342461457 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (4968883217507887 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (24219335239106342180334603435448762166466122567 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (684347342461457 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (684347342461457 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (-1615066472968247 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (684347342461457 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (684347342461457 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (684347342461457 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-1950448147422211 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (7796141952471623 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-4404707654892817 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-10505132458575037 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (3992550377186207 /
    300000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf757_polynomial_eq :
    lowerPullbackPolynomial 21 3 majorizationTriangle757 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray757 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 21 3 majorizationTriangle757
    cellMatrix_21_3 cellMatrix_21_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf757_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray757 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf757_kernel {p : ℝ × ℝ} (hp : majorizationTriangle757.Contains p) :
    (0 : ℝ) ≤ kernel (((21 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 21 3 majorizationTriangle757
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray757
    majorizationLeaf757_polynomial_eq majorizationLeaf757_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
