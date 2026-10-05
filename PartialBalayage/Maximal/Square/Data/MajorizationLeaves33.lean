/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices33

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

/-- The actual closed rational triangle of majorization leaf 780. -/
def majorizationTriangle780 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 780. -/
def majorizationArray780 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (242639737768619225617690060749127271915075406257 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-44475094472380241065902449615158520633674054379 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (2453520659103157 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-2453520659103157 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-44475094472380241065902449615158520633674054379 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (2453520659103157 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-2453520659103157 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (2453520659103157 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (2453520659103157 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-2453520659103157 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (2453520659103157 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-2453520659103157 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-2453520659103157 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (2453520659103157 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-2453520659103157 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (2453520659103157 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf780_polynomial_eq :
    lowerPullbackPolynomial 23 3 majorizationTriangle780 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray780 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 23 3 majorizationTriangle780
    cellMatrix_23_3 cellMatrix_23_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf780_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray780 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf780_kernel {p : ℝ × ℝ} (hp : majorizationTriangle780.Contains p) :
    (0 : ℝ) ≤ kernel (((23 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 23 3 majorizationTriangle780
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray780
    majorizationLeaf780_polynomial_eq majorizationLeaf780_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 781. -/
def majorizationTriangle781 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 781. -/
def majorizationArray781 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 3) then (2453520659103157 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf781_polynomial_eq :
    lowerPullbackPolynomial 23 3 majorizationTriangle781 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray781 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 23 3 majorizationTriangle781
    cellMatrix_23_3 cellMatrix_23_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf781_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray781 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf781_kernel {p : ℝ × ℝ} (hp : majorizationTriangle781.Contains p) :
    (0 : ℝ) ≤ kernel (((23 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 23 3 majorizationTriangle781
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray781
    majorizationLeaf781_polynomial_eq majorizationLeaf781_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 782. -/
def majorizationTriangle782 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 782. -/
def majorizationArray782 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf782_polynomial_eq :
    lowerPullbackPolynomial 23 4 majorizationTriangle782 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray782 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 23 4 majorizationTriangle782
    cellMatrix_23_4 cellMatrix_23_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf782_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray782 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf782_kernel {p : ℝ × ℝ} (hp : majorizationTriangle782.Contains p) :
    (0 : ℝ) ≤ kernel (((23 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 23 4 majorizationTriangle782
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray782
    majorizationLeaf782_polynomial_eq majorizationLeaf782_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 783. -/
def majorizationTriangle783 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 783. -/
def majorizationArray783 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (596350387108975692302154507844390368931627429787 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 2) then (-3885713325449297 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (10562709272820751 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-68866231275603284691492876751409191990464905689 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 2) then (-1537787333357 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (1099044065527211 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-151758644216987 /
    37500000000000000 : ℚ) else
  if p = (2, 2) then (486290835931171 /
    12500000000000000 : ℚ) else
  if p = (2, 3) then (-866240091837649 /
    37500000000000000 : ℚ) else
  if p = (3, 0) then (102026405330371 /
    18000000000000000 : ℚ) else
  if p = (3, 2) then (-1166790448768139 /
    60000000000000000 : ℚ) else
  if p = (3, 3) then (3938143627715273 /
    360000000000000000 : ℚ) else
  if p = (0, 1) then (-16025129657483027453005954908490898172927202803 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf783_polynomial_eq :
    lowerPullbackPolynomial 24 0 majorizationTriangle783 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray783 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 24 0 majorizationTriangle783
    cellMatrix_24_0 cellMatrix_24_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf783_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray783 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf783_kernel {p : ℝ × ℝ} (hp : majorizationTriangle783.Contains p) :
    (0 : ℝ) ≤ kernel (((24 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 24 0 majorizationTriangle783
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray783
    majorizationLeaf783_polynomial_eq majorizationLeaf783_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 784. -/
def majorizationTriangle784 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 784. -/
def majorizationArray784 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (6174908873574546248755315514212323186934207177 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (23590450755003188114443939976424869065069499207 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (23590450755003188114443939976424869065069499207 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (1943625556391327 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (1943625556391327 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-1943625556391327 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (1943625556391327 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (1943625556391327 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-1943625556391327 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (1022070958286141 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-243006055785761 /
    40000000000000000 : ℚ) else
  if p = (3, 2) then (-320912546035799 /
    24000000000000000 : ℚ) else
  if p = (3, 3) then (3938143627715273 /
    360000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf784_polynomial_eq :
    lowerPullbackPolynomial 24 0 majorizationTriangle784 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray784 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 24 0 majorizationTriangle784
    cellMatrix_24_0 cellMatrix_24_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf784_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray784 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf784_kernel {p : ℝ × ℝ} (hp : majorizationTriangle784.Contains p) :
    (0 : ℝ) ≤ kernel (((24 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 24 0 majorizationTriangle784
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray784
    majorizationLeaf784_polynomial_eq majorizationLeaf784_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 785. -/
def majorizationTriangle785 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 785. -/
def majorizationArray785 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (67646022126390062539188190763010391937007128707 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 1) then (-29941905149960459412075599599791462815222797127 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (930427540640719 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (-1696851918395017 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-30719088583186391411185951222737842339506885447 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (1092892916193783 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (1095968490860497 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-730133064795879 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (146957923912959 /
    12500000000000000 : ℚ) else
  if p = (2, 1) then (106341580024693 /
    12500000000000000 : ℚ) else
  if p = (2, 2) then (-189974627953239 /
    6250000000000000 : ℚ) else
  if p = (2, 3) then (1033506187694741 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (-1022070958286141 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-243006055785761 /
    40000000000000000 : ℚ) else
  if p = (3, 2) then (320912546035799 /
    24000000000000000 : ℚ) else
  if p = (3, 3) then (-680778337196617 /
    120000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf785_polynomial_eq :
    lowerPullbackPolynomial 24 1 majorizationTriangle785 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray785 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 24 1 majorizationTriangle785
    cellMatrix_24_1 cellMatrix_24_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf785_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray785 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf785_kernel {p : ℝ × ℝ} (hp : majorizationTriangle785.Contains p) :
    (0 : ℝ) ≤ kernel (((24 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 24 1 majorizationTriangle785
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray785
    majorizationLeaf785_polynomial_eq majorizationLeaf785_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 786. -/
def majorizationTriangle786 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 786. -/
def majorizationArray786 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (32497214358872138161475135455980843945112687 /
    792281625142643375935439503360000000000000000 : ℚ) else
  if p = (0, 1) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 3) then (1943625556391327 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 3) then (1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (2, 3) then (1943625556391327 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (54721535176357 /
    45000000000000000 : ℚ) else
  if p = (3, 1) then (54721535176357 /
    15000000000000000 : ℚ) else
  if p = (3, 2) then (54721535176357 /
    15000000000000000 : ℚ) else
  if p = (3, 3) then (-680778337196617 /
    120000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf786_polynomial_eq :
    lowerPullbackPolynomial 24 1 majorizationTriangle786 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray786 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 24 1 majorizationTriangle786
    cellMatrix_24_1 cellMatrix_24_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf786_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray786 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf786_kernel {p : ℝ × ℝ} (hp : majorizationTriangle786.Contains p) :
    (0 : ℝ) ≤ kernel (((24 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 24 1 majorizationTriangle786
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray786
    majorizationLeaf786_polynomial_eq majorizationLeaf786_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 787. -/
def majorizationTriangle787 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 787. -/
def majorizationArray787 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (242220368443974584141350210350055060788423952817 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-44055725147735599589562599216086309507022600939 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (54721535176357 /
    15000000000000000 : ℚ) else
  if p = (0, 3) then (-54721535176357 /
    45000000000000000 : ℚ) else
  if p = (1, 0) then (-44055725147735599589562599216086309507022600939 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (54721535176357 /
    5000000000000000 : ℚ) else
  if p = (1, 2) then (-54721535176357 /
    5000000000000000 : ℚ) else
  if p = (1, 3) then (54721535176357 /
    15000000000000000 : ℚ) else
  if p = (2, 0) then (54721535176357 /
    15000000000000000 : ℚ) else
  if p = (2, 1) then (-54721535176357 /
    5000000000000000 : ℚ) else
  if p = (2, 2) then (54721535176357 /
    5000000000000000 : ℚ) else
  if p = (2, 3) then (-54721535176357 /
    15000000000000000 : ℚ) else
  if p = (3, 0) then (-54721535176357 /
    45000000000000000 : ℚ) else
  if p = (3, 1) then (54721535176357 /
    15000000000000000 : ℚ) else
  if p = (3, 2) then (-54721535176357 /
    15000000000000000 : ℚ) else
  if p = (3, 3) then (54721535176357 /
    45000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf787_polynomial_eq :
    lowerPullbackPolynomial 24 2 majorizationTriangle787 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray787 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 24 2 majorizationTriangle787
    cellMatrix_24_2 cellMatrix_24_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf787_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray787 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf787_kernel {p : ℝ × ℝ} (hp : majorizationTriangle787.Contains p) :
    (0 : ℝ) ≤ kernel (((24 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 24 2 majorizationTriangle787
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray787
    majorizationLeaf787_polynomial_eq majorizationLeaf787_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 788. -/
def majorizationTriangle788 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 788. -/
def majorizationArray788 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 3) then (54721535176357 /
    45000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf788_polynomial_eq :
    lowerPullbackPolynomial 24 2 majorizationTriangle788 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray788 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 24 2 majorizationTriangle788
    cellMatrix_24_2 cellMatrix_24_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf788_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray788 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf788_kernel {p : ℝ × ℝ} (hp : majorizationTriangle788.Contains p) :
    (0 : ℝ) ≤ kernel (((24 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 24 2 majorizationTriangle788
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray788
    majorizationLeaf788_polynomial_eq majorizationLeaf788_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 789. -/
def majorizationTriangle789 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 789. -/
def majorizationArray789 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf789_polynomial_eq :
    lowerPullbackPolynomial 24 3 majorizationTriangle789 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray789 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 24 3 majorizationTriangle789
    cellMatrix_24_3 cellMatrix_24_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf789_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray789 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf789_kernel {p : ℝ × ℝ} (hp : majorizationTriangle789.Contains p) :
    (0 : ℝ) ≤ kernel (((24 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 24 3 majorizationTriangle789
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray789
    majorizationLeaf789_polynomial_eq majorizationLeaf789_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
