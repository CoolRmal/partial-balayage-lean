/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices7

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

/-- The actual closed rational triangle of majorization leaf 396. -/
def majorizationTriangle396 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 396. -/
def majorizationArray396 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (16090070597333655025522755355824390048620411483 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (0, 1) then (-21098072079964391910343044424078009079579354873 /
    190147590034234410224505480806400000000000000000 : ℚ) else
  if p = (0, 2) then (-2326888284051849 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (14014454035273 /
    28125000000000000 : ℚ) else
  if p = (1, 0) then (-4308512504592927427395365640403745034889503077 /
    38029518006846882044901096161280000000000000000 : ℚ) else
  if p = (1, 1) then (-901539428338341 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (660311053172867 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-115265819899447 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-98858456527167 /
    8000000000000000 : ℚ) else
  if p = (2, 1) then (750701995303261 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-58116342083103 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (147745863819071 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (20039553344959 /
    14400000000000000 : ℚ) else
  if p = (3, 1) then (-12321147781579 /
    24000000000000000 : ℚ) else
  if p = (3, 2) then (142733765939399 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-72627575341331 /
    360000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf396_polynomial_eq :
    lowerPullbackPolynomial 8 6 majorizationTriangle396 radialPowerData14.radius
      (certifiedRadialHeight radialPowerData14 radialPowerData32)
      (certifiedRadialSlope radialPowerData14) 1 =
        planeArrayPolynomial majorizationArray396 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 6 majorizationTriangle396
    cellMatrix_8_6 cellMatrix_8_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf396_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray396 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf396_kernel {p : ℝ × ℝ} (hp : majorizationTriangle396.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 6 majorizationTriangle396
    radialPowerData14 radialPowerData32 radialPowerData14_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray396
    majorizationLeaf396_polynomial_eq majorizationLeaf396_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 397. -/
def majorizationTriangle397 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 397. -/
def majorizationArray397 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (33185802142317438568732629270702293970262993 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (386089236635467231 /
    3000000000000000000 : ℚ) else
  if p = (0, 2) then (-5691670532272213 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-12357508557293 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (387276737450474911 /
    3000000000000000000 : ℚ) else
  if p = (1, 1) then (-620755350018069 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (11336302746923 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-77739233676053 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-4092610151623153 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-79331262743041 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-215494093544629 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (22548716356171 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-25717523525203 /
    28125000000000000 : ℚ) else
  if p = (3, 1) then (-96424759841833 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (27550513845907 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (-72627575341331 /
    360000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf397_polynomial_eq :
    lowerPullbackPolynomial 8 6 majorizationTriangle397 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray397 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 6 majorizationTriangle397
    cellMatrix_8_6 cellMatrix_8_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf397_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray397 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf397_kernel {p : ℝ × ℝ} (hp : majorizationTriangle397.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 6 majorizationTriangle397
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray397
    majorizationLeaf397_polynomial_eq majorizationLeaf397_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 398. -/
def majorizationTriangle398 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 398. -/
def majorizationArray398 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (43432882241958523544946562222132795893789461269 /
    356526731314189519170947776512000000000000000000 : ℚ) else
  if p = (0, 1) then (-336414121246129781 /
    3000000000000000000 : ℚ) else
  if p = (0, 2) then (-243349591755923 /
    24000000000000000 : ℚ) else
  if p = (0, 3) then (365705318765189 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-338121028406178421 /
    3000000000000000000 : ℚ) else
  if p = (1, 1) then (-3648138314943759 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (199247773575079 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-25487371692321 /
    40000000000000000 : ℚ) else
  if p = (2, 0) then (-1147706331447229 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (465030302110373 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (4910017222627 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-219304379455121 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (25717523525203 /
    28125000000000000 : ℚ) else
  if p = (3, 1) then (-96424759841833 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (-27550513845907 /
    75000000000000000 : ℚ) else
  if p = (3, 3) then (18033412670951 /
    60000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf398_polynomial_eq :
    lowerPullbackPolynomial 8 7 majorizationTriangle398 radialPowerData15.radius
      (certifiedRadialHeight radialPowerData15 radialPowerData32)
      (certifiedRadialSlope radialPowerData15) 1 =
        planeArrayPolynomial majorizationArray398 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 7 majorizationTriangle398
    cellMatrix_8_7 cellMatrix_8_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf398_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray398 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf398_kernel {p : ℝ × ℝ} (hp : majorizationTriangle398.Contains p) :
    (1 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 7 majorizationTriangle398
    radialPowerData15 radialPowerData32 radialPowerData15_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray398
    majorizationLeaf398_polynomial_eq majorizationLeaf398_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 399. -/
def majorizationTriangle399 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 399. -/
def majorizationArray399 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (31023476690864571457437942458752591485635710571 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (126719840774548650591266984098101659534692063913 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-143484466741973 /
    12000000000000000 : ℚ) else
  if p = (0, 3) then (494184268275479 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (123351185949280528684200793068874929004794223273 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-2141791913785601 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (584235387366967 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-385711490662337 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-18472037609059 /
    2400000000000000 : ℚ) else
  if p = (2, 1) then (9371353651661 /
    4000000000000000 : ℚ) else
  if p = (2, 2) then (-166202425890731 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (38970252745611 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-184307217668879 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-142752440386657 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-160299134680637 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (18033412670951 /
    60000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf399_polynomial_eq :
    lowerPullbackPolynomial 8 7 majorizationTriangle399 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray399 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 7 majorizationTriangle399
    cellMatrix_8_7 cellMatrix_8_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf399_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray399 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf399_kernel {p : ℝ × ℝ} (hp : majorizationTriangle399.Contains p) :
    (0 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 7 majorizationTriangle399
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray399
    majorizationLeaf399_polynomial_eq majorizationLeaf399_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 400. -/
def majorizationTriangle400 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 400. -/
def majorizationArray400 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2829395016264344489599737678734292658315080421739 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-108132037084918362159219485906930677853104249513 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-1246655959400627 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (184307217668879 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-108132037084918362159219485906930677853104249513 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-226997083948651 /
    12500000000000000 : ℚ) else
  if p = (1, 2) then (-22882850226217 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (-142752440386657 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-1246655959400627 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-22882850226217 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (-40812695071421 /
    12500000000000000 : ℚ) else
  if p = (2, 3) then (160299134680637 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (184307217668879 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-142752440386657 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (160299134680637 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-2873343183577799 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf400_polynomial_eq :
    lowerPullbackPolynomial 8 8 majorizationTriangle400 radialPowerData16.radius
      (certifiedRadialHeight radialPowerData16 radialPowerData32)
      (certifiedRadialSlope radialPowerData16) 0 =
        planeArrayPolynomial majorizationArray400 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 8 majorizationTriangle400
    cellMatrix_8_8 cellMatrix_8_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf400_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray400 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf400_kernel {p : ℝ × ℝ} (hp : majorizationTriangle400.Contains p) :
    (0 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 8 majorizationTriangle400
    radialPowerData16 radialPowerData32 radialPowerData16_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray400
    majorizationLeaf400_polynomial_eq majorizationLeaf400_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 401. -/
def majorizationTriangle401 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 401. -/
def majorizationArray401 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (51994295793103540226610764254087860593365904011 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (24090077844622026719911762590878947152909092483 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (-1244701510315261 /
    60000000000000000 : ℚ) else
  if p = (0, 3) then (43939931383783 /
    15000000000000000 : ℚ) else
  if p = (1, 0) then (24090077844622026719911762590878947152909092483 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (-6005760043122717 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (3279732741970149 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-1347748677301591 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-1244701510315261 /
    60000000000000000 : ℚ) else
  if p = (2, 1) then (3279732741970149 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-2879246474787893 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (452174008149527 /
    50000000000000000 : ℚ) else
  if p = (3, 0) then (43939931383783 /
    15000000000000000 : ℚ) else
  if p = (3, 1) then (-1347748677301591 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (452174008149527 /
    50000000000000000 : ℚ) else
  if p = (3, 3) then (-2873343183577799 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf401_polynomial_eq :
    lowerPullbackPolynomial 8 8 majorizationTriangle401 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray401 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 8 8 majorizationTriangle401
    cellMatrix_8_8 cellMatrix_8_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf401_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray401 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf401_kernel {p : ℝ × ℝ} (hp : majorizationTriangle401.Contains p) :
    (0 : ℝ) ≤ kernel (((8 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 8 8 majorizationTriangle401
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray401
    majorizationLeaf401_polynomial_eq majorizationLeaf401_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 423. -/
def majorizationTriangle423 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 423. -/
def majorizationArray423 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (902854405613135071144303401244454201995867777801 /
    570442770102703230673516442419200000000000000000 : ℚ) else
  if p = (0, 2) then (-635075427202601 /
    37500000000000000 : ℚ) else
  if p = (0, 3) then (8218774187769253 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-2371132831662206412768742608954358587309222931 /
    7605903601369376408980219232256000000000000000 : ℚ) else
  if p = (1, 2) then (468078828272507 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (-615268076785613 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-4141362406221139 /
    300000000000000000 : ℚ) else
  if p = (2, 2) then (-120481360461353 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (282431686574623 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (45246463983979 /
    25000000000000000 : ℚ) else
  if p = (3, 2) then (28792090111119 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-158671603203763 /
    1800000000000000000 : ℚ) else
  if p = (0, 1) then (-24060218486654185399029161537316396114038992713 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf423_polynomial_eq :
    lowerPullbackPolynomial 9 0 majorizationTriangle423 radialPowerData9.radius
      (certifiedRadialHeight radialPowerData9 radialPowerData32)
      (certifiedRadialSlope radialPowerData9) 1 =
        planeArrayPolynomial majorizationArray423 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 0 majorizationTriangle423
    cellMatrix_9_0 cellMatrix_9_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf423_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray423 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf423_kernel {p : ℝ × ℝ} (hp : majorizationTriangle423.Contains p) :
    (1 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 0 majorizationTriangle423
    radialPowerData9 radialPowerData32 radialPowerData9_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray423
    majorizationLeaf423_polynomial_eq majorizationLeaf423_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 424. -/
def majorizationTriangle424 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 424. -/
def majorizationArray424 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (65122644877002668141972076329764128806163447847 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (3065523214387312081865508557815021010379954379 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (0, 2) then (4772965289514071 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-84721999762841 /
    14400000000000000 : ℚ) else
  if p = (1, 0) then (7700997517845253399004826517015622190855621217 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (1, 1) then (672416776084113 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (81760038796361 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-1490017164047723 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-5546306339186401 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (212154032411913 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (19403773753357 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (-406191769945483 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-3617331425642867 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (37366695625933 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (-14080937462951 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-158671603203763 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf424_polynomial_eq :
    lowerPullbackPolynomial 9 0 majorizationTriangle424 radialPowerData10.radius
      (certifiedRadialHeight radialPowerData10 radialPowerData32)
      (certifiedRadialSlope radialPowerData10) 1 =
        planeArrayPolynomial majorizationArray424 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 0 majorizationTriangle424
    cellMatrix_9_0 cellMatrix_9_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf424_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray424 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf424_kernel {p : ℝ × ℝ} (hp : majorizationTriangle424.Contains p) :
    (1 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 0 majorizationTriangle424
    radialPowerData10 radialPowerData32 radialPowerData10_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray424
    majorizationLeaf424_polynomial_eq majorizationLeaf424_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 425. -/
def majorizationTriangle425 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 425. -/
def majorizationArray425 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (138004343614682416651808113623810122252951235013 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 1) then (-9337226663462595236850525262242193589840120417 /
    29710560942849126597578981376000000000000000000 : ℚ) else
  if p = (0, 2) then (209211384676563 /
    20000000000000000 : ℚ) else
  if p = (0, 3) then (36681929296147 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (-2324198788854939063259931049710277134638995659 /
    9903520314283042199192993792000000000000000000 : ℚ) else
  if p = (1, 1) then (320889579759401 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (-73594624256553 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (-2395634149461 /
    6250000000000000 : ℚ) else
  if p = (2, 0) then (-763636480402439 /
    50000000000000000 : ℚ) else
  if p = (2, 1) then (-199493755270789 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (41468965651917 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (16549697394259 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (3617331425642867 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (37366695625933 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (14080937462951 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-36602859829991 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf425_polynomial_eq :
    lowerPullbackPolynomial 9 1 majorizationTriangle425 radialPowerData10.radius
      (certifiedRadialHeight radialPowerData10 radialPowerData32)
      (certifiedRadialSlope radialPowerData10) 1 =
        planeArrayPolynomial majorizationArray425 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 1 majorizationTriangle425
    cellMatrix_9_1 cellMatrix_9_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf425_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray425 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf425_kernel {p : ℝ × ℝ} (hp : majorizationTriangle425.Contains p) :
    (1 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 1 majorizationTriangle425
    radialPowerData10 radialPowerData32 radialPowerData10_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray425
    majorizationLeaf425_polynomial_eq majorizationLeaf425_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 426. -/
def majorizationTriangle426 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 426. -/
def majorizationArray426 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5700930657985748483611435261540327904075737757 /
    8913168282854737979273694412800000000000000000 : ℚ) else
  if p = (0, 1) then (228628074667637969550203616977482925374028845009 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (2245600101926437 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (31307231740133 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (194420000778552447774833854104498364321794297809 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-143188350493309 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (274996641544463 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-47064363035707 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-1475555556311551 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (14313345001381 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (43254236821183 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (3503465041473 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-2055133046465371 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (17531128927599 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (47863821013511 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-36602859829991 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf426_polynomial_eq :
    lowerPullbackPolynomial 9 1 majorizationTriangle426 radialPowerData11.radius
      (certifiedRadialHeight radialPowerData11 radialPowerData32)
      (certifiedRadialSlope radialPowerData11) 1 =
        planeArrayPolynomial majorizationArray426 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 1 majorizationTriangle426
    cellMatrix_9_1 cellMatrix_9_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf426_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray426 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf426_kernel {p : ℝ × ℝ} (hp : majorizationTriangle426.Contains p) :
    (1 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 1 majorizationTriangle426
    radialPowerData11 radialPowerData32 radialPowerData11_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray426
    majorizationLeaf426_polynomial_eq majorizationLeaf426_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 427. -/
def majorizationTriangle427 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 427. -/
def majorizationArray427 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (790995834330639522148387107557071793907331638929 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 1) then (-227569486177949147987033619932292268619809099729 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (541369426339481 /
    50000000000000000 : ℚ) else
  if p = (0, 3) then (-239855953006981 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-56400711770838779669232643970840016673713576603 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-247873094831 /
    400000000000000 : ℚ) else
  if p = (1, 2) then (-20468446810017 /
    5000000000000000 : ℚ) else
  if p = (1, 3) then (-105298695486667 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-1668748053029491 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (-33453365892089 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (45559028917347 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (25556345379 /
    40000000000000000 : ℚ) else
  if p = (3, 0) then (2055133046465371 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (17531128927599 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (-47863821013511 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (14684638126981 /
    360000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf427_polynomial_eq :
    lowerPullbackPolynomial 9 2 majorizationTriangle427 radialPowerData11.radius
      (certifiedRadialHeight radialPowerData11 radialPowerData32)
      (certifiedRadialSlope radialPowerData11) 1 =
        planeArrayPolynomial majorizationArray427 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 2 majorizationTriangle427
    cellMatrix_9_2 cellMatrix_9_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf427_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray427 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf427_kernel {p : ℝ × ℝ} (hp : majorizationTriangle427.Contains p) :
    (1 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 2 majorizationTriangle427
    radialPowerData11 radialPowerData32 radialPowerData11_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray427
    majorizationLeaf427_polynomial_eq majorizationLeaf427_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 428. -/
def majorizationTriangle428 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 428. -/
def majorizationArray428 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (7620399249272890350234370445200995595485443519 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (88450003203221762002287777422445050999164257797 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (353030948454889 /
    60000000000000000 : ℚ) else
  if p = (0, 3) then (60055669956499 /
    112500000000000000 : ℚ) else
  if p = (1, 0) then (26571276547805271547274977984287256523190703959 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (-708736040827431 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (290551048789659 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-3888601811299 /
    75000000000000000 : ℚ) else
  if p = (2, 0) then (-2827385169255901 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (-5454919827439 /
    5000000000000000 : ℚ) else
  if p = (2, 2) then (40078752364489 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-7380653581559 /
    60000000000000000 : ℚ) else
  if p = (3, 0) then (-4212066678181363 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-856354656903 /
    40000000000000000 : ℚ) else
  if p = (3, 2) then (22304451392117 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (14684638126981 /
    360000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf428_polynomial_eq :
    lowerPullbackPolynomial 9 2 majorizationTriangle428 radialPowerData12.radius
      (certifiedRadialHeight radialPowerData12 radialPowerData32)
      (certifiedRadialSlope radialPowerData12) 1 =
        planeArrayPolynomial majorizationArray428 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 9 2 majorizationTriangle428
    cellMatrix_9_2 cellMatrix_9_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf428_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray428 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf428_kernel {p : ℝ × ℝ} (hp : majorizationTriangle428.Contains p) :
    (1 : ℝ) ≤ kernel (((9 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 9 2 majorizationTriangle428
    radialPowerData12 radialPowerData32 radialPowerData12_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray428
    majorizationLeaf428_polynomial_eq majorizationLeaf428_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
