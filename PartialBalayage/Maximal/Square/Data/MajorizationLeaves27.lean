/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices27

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

/-- The actual closed rational triangle of majorization leaf 713. -/
def majorizationTriangle713 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 713. -/
def majorizationArray713 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (23945639973301022189300598979272460686219511169 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 1) then (-37521750404874543841788736757216437352333120327 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (3999581610999283 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (-2058604587284741 /
    450000000000000000 : ℚ) else
  if p = (1, 0) then (-37938309888414060147875111102072904114181051207 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (4995863851301487 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (2532789116416283 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-65594954169533 /
    6250000000000000 : ℚ) else
  if p = (2, 0) then (4262467604009987 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (2269903123405579 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-9798556091123349 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (6781441287491117 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-2288629831169107 /
    450000000000000000 : ℚ) else
  if p = (3, 1) then (-245949442114963 /
    25000000000000000 : ℚ) else
  if p = (3, 2) then (6715719789238441 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-1910640673592863 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf713_polynomial_eq :
    lowerPullbackPolynomial 18 7 majorizationTriangle713 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray713 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 7 majorizationTriangle713
    cellMatrix_18_7 cellMatrix_18_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf713_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray713 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf713_kernel {p : ℝ × ℝ} (hp : majorizationTriangle713.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 7 majorizationTriangle713
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray713
    majorizationLeaf713_polynomial_eq majorizationLeaf713_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 714. -/
def majorizationTriangle714 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 714. -/
def majorizationArray714 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (32497214358872138161475135455980843945112687 /
    792281625142643375935439503360000000000000000 : ℚ) else
  if p = (0, 1) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 3) then (3632883487353533 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 3) then (3632883487353533 /
    600000000000000000 : ℚ) else
  if p = (2, 3) then (3632883487353533 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (752865296771777 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (752865296771777 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (752865296771777 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (-1910640673592863 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf714_polynomial_eq :
    lowerPullbackPolynomial 18 7 majorizationTriangle714 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray714 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 7 majorizationTriangle714
    cellMatrix_18_7 cellMatrix_18_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf714_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray714 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf714_kernel {p : ℝ × ℝ} (hp : majorizationTriangle714.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 7 majorizationTriangle714
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray714
    majorizationLeaf714_polynomial_eq majorizationLeaf714_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 715. -/
def majorizationTriangle715 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 715. -/
def majorizationArray715 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (244716792506787047969564051033553058702345898417 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-46552149210548063417776439899584307420944546539 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (752865296771777 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (-752865296771777 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (-46552149210548063417776439899584307420944546539 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (752865296771777 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-752865296771777 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (752865296771777 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (752865296771777 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (-752865296771777 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (752865296771777 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (-752865296771777 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (-752865296771777 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (752865296771777 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (-752865296771777 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (752865296771777 /
    360000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf715_polynomial_eq :
    lowerPullbackPolynomial 18 8 majorizationTriangle715 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray715 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 8 majorizationTriangle715
    cellMatrix_18_8 cellMatrix_18_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf715_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray715 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf715_kernel {p : ℝ × ℝ} (hp : majorizationTriangle715.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 8 majorizationTriangle715
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray715
    majorizationLeaf715_polynomial_eq majorizationLeaf715_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 716. -/
def majorizationTriangle716 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 716. -/
def majorizationArray716 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 3) then (752865296771777 /
    360000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf716_polynomial_eq :
    lowerPullbackPolynomial 18 8 majorizationTriangle716 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray716 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 8 majorizationTriangle716
    cellMatrix_18_8 cellMatrix_18_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf716_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray716 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf716_kernel {p : ℝ × ℝ} (hp : majorizationTriangle716.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 8 majorizationTriangle716
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray716
    majorizationLeaf716_polynomial_eq majorizationLeaf716_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 717. -/
def majorizationTriangle717 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 717. -/
def majorizationArray717 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf717_polynomial_eq :
    lowerPullbackPolynomial 18 9 majorizationTriangle717 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray717 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 18 9 majorizationTriangle717
    cellMatrix_18_9 cellMatrix_18_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf717_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray717 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf717_kernel {p : ℝ × ℝ} (hp : majorizationTriangle717.Contains p) :
    (0 : ℝ) ≤ kernel (((18 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 18 9 majorizationTriangle717
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray717
    majorizationLeaf717_polynomial_eq majorizationLeaf717_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 718. -/
def majorizationTriangle718 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 718. -/
def majorizationArray718 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (114385481826527986508247028138055146758883131893 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 2) then (-193076582397667 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (63472175552897 /
    360000000000000000 : ℚ) else
  if p = (1, 0) then (-3671778637204737626638087060755390859594157579 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (1, 2) then (-76686717474957 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (6883649786149 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-322140108979819 /
    300000000000000000 : ℚ) else
  if p = (2, 2) then (-35628953969143 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (103462291664647 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-15555385383 /
    390625000000000 : ℚ) else
  if p = (3, 2) then (29549627897323 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-108598203824509 /
    450000000000000000 : ℚ) else
  if p = (0, 1) then (-3272755743216346964409727541482548270578257419 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf718_polynomial_eq :
    lowerPullbackPolynomial 19 0 majorizationTriangle718 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray718 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 0 majorizationTriangle718
    cellMatrix_19_0 cellMatrix_19_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf718_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray718 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf718_kernel {p : ℝ × ℝ} (hp : majorizationTriangle718.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 0 majorizationTriangle718
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray718
    majorizationLeaf718_polynomial_eq majorizationLeaf718_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 719. -/
def majorizationTriangle719 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 719. -/
def majorizationArray719 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2086611148526392436560453344257088348216175259 /
    4456584141427368989636847206400000000000000000 : ℚ) else
  if p = (0, 1) then (4563142753289947677776293480922661492660969251 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (0, 2) then (-668743539257159 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-71335295606279 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (5199816117379343349304779064228390682773757731 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 1) then (-457767549067689 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (339176065625141 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-220584582182593 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-145754075820187 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (23770160948417 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (-224890664187737 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (110310174544463 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-12910635504457 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-997466006627 /
    7500000000000000 : ℚ) else
  if p = (3, 2) then (128547523957049 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-108598203824509 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf719_polynomial_eq :
    lowerPullbackPolynomial 19 0 majorizationTriangle719 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray719 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 0 majorizationTriangle719
    cellMatrix_19_0 cellMatrix_19_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf719_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray719 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf719_kernel {p : ℝ × ℝ} (hp : majorizationTriangle719.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 0 majorizationTriangle719
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray719
    majorizationLeaf719_polynomial_eq majorizationLeaf719_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 720. -/
def majorizationTriangle720 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 720. -/
def majorizationArray720 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (98844815310757737726507326876517543457289799073 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-1484848649178006373250858392242716131737930337 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (0, 2) then (-68792287030849 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-987342734491009 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-5052911057482092201476645282220388483059228451 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 1) then (-299863220113679 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-29297957032753 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-134344277994491 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-754591650109849 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-1562140968477 /
    8000000000000000 : ℚ) else
  if p = (2, 2) then (32204383726361 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-184039217891581 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (12910635504457 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-997466006627 /
    7500000000000000 : ℚ) else
  if p = (3, 2) then (-128547523957049 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (201070503429839 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf720_polynomial_eq :
    lowerPullbackPolynomial 19 1 majorizationTriangle720 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray720 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 1 majorizationTriangle720
    cellMatrix_19_1 cellMatrix_19_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf720_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray720 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf720_kernel {p : ℝ × ℝ} (hp : majorizationTriangle720.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 1 majorizationTriangle720
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray720
    majorizationLeaf720_polynomial_eq majorizationLeaf720_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 721. -/
def majorizationTriangle721 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 721. -/
def majorizationArray721 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (7012300795653189424472970913800626982688765579 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (70069825706455463723518048298377731161308555343 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-451738686921757 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (1138211208429869 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (79643806547330658583606689664863828786847443023 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-208565095094067 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (18658382841719 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (301859299941703 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-569875995031313 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-6451332838777 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (197676065820019 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-24809711833111 /
    24000000000000000 : ℚ) else
  if p = (3, 0) then (22571712575563 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (210294637361 /
    600000000000000 : ℚ) else
  if p = (3, 2) then (-273593482902629 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (201070503429839 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf721_polynomial_eq :
    lowerPullbackPolynomial 19 1 majorizationTriangle721 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray721 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 1 majorizationTriangle721
    cellMatrix_19_1 cellMatrix_19_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf721_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray721 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf721_kernel {p : ℝ × ℝ} (hp : majorizationTriangle721.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 1 majorizationTriangle721
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray721
    majorizationLeaf721_polynomial_eq majorizationLeaf721_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 722. -/
def majorizationTriangle722 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 722. -/
def majorizationArray722 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1355767650042769923270058667912597485573398548429 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-22063964920816522136360600269338755638814319301 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-528067510760929 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-908131039113509 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-76317918761491056688447779313850519810976016463 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-7271870684357 /
    2000000000000000 : ℚ) else
  if p = (1, 2) then (-17552128947391 /
    12500000000000000 : ℚ) else
  if p = (1, 3) then (80382032269487 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-479589144729061 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-4958874207837 /
    6250000000000000 : ℚ) else
  if p = (2, 2) then (-7591741708261 /
    10000000000000000 : ℚ) else
  if p = (2, 3) then (492032854175581 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-22571712575563 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (210294637361 /
    600000000000000 : ℚ) else
  if p = (3, 2) then (273593482902629 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-291162774176081 /
    180000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf722_polynomial_eq :
    lowerPullbackPolynomial 19 2 majorizationTriangle722 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray722 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 2 majorizationTriangle722
    cellMatrix_19_2 cellMatrix_19_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf722_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray722 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf722_kernel {p : ℝ × ℝ} (hp : majorizationTriangle722.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 2 majorizationTriangle722
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray722
    majorizationLeaf722_polynomial_eq majorizationLeaf722_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 723. -/
def majorizationTriangle723 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 723. -/
def majorizationArray723 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5685704977281278220818380877655157825680041603 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (72430151348091468533895035979310103556415119581 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-3427176675609221 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (1620221927922193 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (80525759952585913503777221088881087581150863581 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-2595309848344331 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (13789861618277 /
    1600000000000000 : ℚ) else
  if p = (1, 3) then (-562138645533729 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-2218458494597093 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (1577279961594937 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-2024242755945191 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (2419594887585229 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (40987831643327 /
    90000000000000000 : ℚ) else
  if p = (3, 1) then (-803479586394647 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (73888774248611 /
    18750000000000000 : ℚ) else
  if p = (3, 3) then (-291162774176081 /
    180000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf723_polynomial_eq :
    lowerPullbackPolynomial 19 2 majorizationTriangle723 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray723 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 19 2 majorizationTriangle723
    cellMatrix_19_2 cellMatrix_19_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf723_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray723 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf723_kernel {p : ℝ × ℝ} (hp : majorizationTriangle723.Contains p) :
    (0 : ℝ) ≤ kernel (((19 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 19 2 majorizationTriangle723
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray723
    majorizationLeaf723_polynomial_eq majorizationLeaf723_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
