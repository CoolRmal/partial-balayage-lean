/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices2

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

/-- The actual closed rational triangle of majorization leaf 212. -/
def majorizationTriangle212 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 212. -/
def majorizationArray212 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (917746354752465831241191960460381759577159115827 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 1) then (-530846274146782800055595170044447300981088114967 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (-7377280807705339 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (103815951346108903 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (162633765619897124834545949469367138058657277673 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (88707987224621289 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (10873098238833773 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-126634005791675731 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-80705964746125663 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-60702494405706323 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-55423309610813403 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (140762961137334871 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (134489892106776233 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (50925756162379597 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (54397328152406351 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-296802388014804373 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf212_polynomial_eq :
    lowerPullbackPolynomial 4 2 majorizationTriangle212 radialPowerData6.radius
      (certifiedRadialHeight radialPowerData6 radialPowerData32)
      (certifiedRadialSlope radialPowerData6) 1 =
        planeArrayPolynomial majorizationArray212 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 4 2 majorizationTriangle212
    cellMatrix_4_2 cellMatrix_4_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf212_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray212 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf212_kernel {p : ℝ × ℝ} (hp : majorizationTriangle212.Contains p) :
    (1 : ℝ) ≤ kernel (((4 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 4 2 majorizationTriangle212
    radialPowerData6 radialPowerData32 radialPowerData6_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray212
    majorizationLeaf212_polynomial_eq majorizationLeaf212_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 213. -/
def majorizationTriangle213 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 213. -/
def majorizationArray213 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (9599040957847541331575583704306727396756583453 /
    7922816251426433759354395033600000000000000000 : ℚ) else
  if p = (0, 1) then (70161141962285966882759242376036698447816736333 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (8231759076908331 /
    200000000000000000 : ℚ) else
  if p = (0, 3) then (4396753248631727 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-8717572348039726883518817009472412521505964467 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (27042599776668709 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-10897645076132059 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (12981444951183649 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-51770875658978907 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (27105166900275461 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-16302447198541683 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (15276465740134631 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-19207094629541213 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (-68540987773806037 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (121202529931199011 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-296802388014804373 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf213_polynomial_eq :
    lowerPullbackPolynomial 4 2 majorizationTriangle213 radialPowerData7.radius
      (certifiedRadialHeight radialPowerData7 radialPowerData32)
      (certifiedRadialSlope radialPowerData7) 1 =
        planeArrayPolynomial majorizationArray213 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 4 2 majorizationTriangle213
    cellMatrix_4_2 cellMatrix_4_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf213_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray213 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf213_kernel {p : ℝ × ℝ} (hp : majorizationTriangle213.Contains p) :
    (1 : ℝ) ≤ kernel (((4 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 4 2 majorizationTriangle213
    radialPowerData7 radialPowerData32 radialPowerData7_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray213
    majorizationLeaf213_polynomial_eq majorizationLeaf213_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 214. -/
def majorizationTriangle214 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 214. -/
def majorizationArray214 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (276446058969191253852833524782985971428705321 /
    348170636049013202315378688000000000000000000 : ℚ) else
  if p = (0, 1) then (-25061489935539972061733845678607818924709134191 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (0, 2) then (185500060269101789 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (6317892889106299 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (100678098895992917140201230124651273201443357107 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (-55829041970392443 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-198902520389182597 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (148929438912935819 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-12358775360530657 /
    24000000000000000 : ℚ) else
  if p = (2, 1) then (109976808647336613 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (226102612663856339 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-1852902706153441 /
    2400000000000000 : ℚ) else
  if p = (3, 0) then (19207094629541213 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (-68540987773806037 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-121202529931199011 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (542097167488049173 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf214_polynomial_eq :
    lowerPullbackPolynomial 4 3 majorizationTriangle214 radialPowerData7.radius
      (certifiedRadialHeight radialPowerData7 radialPowerData32)
      (certifiedRadialSlope radialPowerData7) 1 =
        planeArrayPolynomial majorizationArray214 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 4 3 majorizationTriangle214
    cellMatrix_4_3 cellMatrix_4_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf214_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray214 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf214_kernel {p : ℝ × ℝ} (hp : majorizationTriangle214.Contains p) :
    (1 : ℝ) ≤ kernel (((4 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 4 3 majorizationTriangle214
    radialPowerData7 radialPowerData32 radialPowerData7_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray214
    majorizationLeaf214_polynomial_eq majorizationLeaf214_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 215. -/
def majorizationTriangle215 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 215. -/
def majorizationArray215 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (3134333748691150602512883515238328391672932197 /
    3961408125713216879677197516800000000000000000 : ℚ) else
  if p = (0, 1) then (48863285946551905502410289704404876771718674211 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (20205865282359787 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (-32179971487811243 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-61909844909950225229109237000053800618009479389 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-18828708916933431 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (7559766268666763 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (-28831769254266563 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-6888799277456641 /
    20000000000000000 : ℚ) else
  if p = (2, 1) then (-1197589353270631 /
    12500000000000000 : ℚ) else
  if p = (2, 2) then (1564226093778681 /
    5000000000000000 : ℚ) else
  if p = (2, 3) then (-26290496983229641 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (442707181705651411 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-15958985556871789 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (-299692107625651151 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (542097167488049173 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf215_polynomial_eq :
    lowerPullbackPolynomial 4 3 majorizationTriangle215 radialPowerData8.radius
      (certifiedRadialHeight radialPowerData8 radialPowerData32)
      (certifiedRadialSlope radialPowerData8) 1 =
        planeArrayPolynomial majorizationArray215 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 4 3 majorizationTriangle215
    cellMatrix_4_3 cellMatrix_4_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf215_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray215 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf215_kernel {p : ℝ × ℝ} (hp : majorizationTriangle215.Contains p) :
    (1 : ℝ) ≤ kernel (((4 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 4 3 majorizationTriangle215
    radialPowerData8 radialPowerData32 radialPowerData8_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray215
    majorizationLeaf215_polynomial_eq majorizationLeaf215_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 216. -/
def majorizationTriangle216 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 216. -/
def majorizationArray216 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (308220813819476267772997289409897293408839358573 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 1) then (16757178274219388489036139794694028113887423903 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (0, 2) then (236043203381952181 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-442707181705651411 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (16757178274219388489036139794694028113887423903 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (1, 1) then (-155775204922885999 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (98956357436689041 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-15958985556871789 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (236043203381952181 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (98956357436689041 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-237123063874503911 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (299692107625651151 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-442707181705651411 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-15958985556871789 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (299692107625651151 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-891597116686589 /
    4000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf216_polynomial_eq :
    lowerPullbackPolynomial 4 4 majorizationTriangle216 radialPowerData8.radius
      (certifiedRadialHeight radialPowerData8 radialPowerData32)
      (certifiedRadialSlope radialPowerData8) 1 =
        planeArrayPolynomial majorizationArray216 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 4 4 majorizationTriangle216
    cellMatrix_4_4 cellMatrix_4_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf216_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray216 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf216_kernel {p : ℝ × ℝ} (hp : majorizationTriangle216.Contains p) :
    (1 : ℝ) ≤ kernel (((4 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 4 4 majorizationTriangle216
    radialPowerData8 radialPowerData32 radialPowerData8_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray216
    majorizationLeaf216_polynomial_eq majorizationLeaf216_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 217. -/
def majorizationTriangle217 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 217. -/
def majorizationArray217 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (52597209311149569132937396810951104206615705647 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (601975642395032199893856443998868737500360521 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (0, 2) then (-62999152996581121 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (184234344690739843 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (601975642395032199893856443998868737500360521 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (1, 1) then (-14096431649844763 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-42772922271310677 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (118370584957978307 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-62999152996581121 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-42772922271310677 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-38957551132166659 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (101526594883313899 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (184234344690739843 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (118370584957978307 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (101526594883313899 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-891597116686589 /
    4000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf217_polynomial_eq :
    lowerPullbackPolynomial 4 4 majorizationTriangle217 radialPowerData9.radius
      (certifiedRadialHeight radialPowerData9 radialPowerData32)
      (certifiedRadialSlope radialPowerData9) 1 =
        planeArrayPolynomial majorizationArray217 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 4 4 majorizationTriangle217
    cellMatrix_4_4 cellMatrix_4_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf217_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray217 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf217_kernel {p : ℝ × ℝ} (hp : majorizationTriangle217.Contains p) :
    (1 : ℝ) ≤ kernel (((4 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 4 4 majorizationTriangle217
    radialPowerData9 radialPowerData32 radialPowerData9_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray217
    majorizationLeaf217_polynomial_eq majorizationLeaf217_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 255. -/
def majorizationTriangle255 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 255. -/
def majorizationArray255 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (492737220511713871327661945825757492369789168953 /
    114088554020540646134703288483840000000000000000 : ℚ) else
  if p = (0, 2) then (-57970003719659893 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (7856601797951633 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (-48690108077322472428521523301916196400153427629 /
    63382530011411470074835160268800000000000000000 : ℚ) else
  if p = (1, 2) then (14013198261038133 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-2656943129816207 /
    50000000000000000 : ℚ) else
  if p = (2, 0) then (-28733404922016883 /
    300000000000000000 : ℚ) else
  if p = (2, 2) then (-5720735118600229 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (85245513088939 /
    4000000000000000 : ℚ) else
  if p = (3, 0) then (3941132597262341 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (48888610002163 /
    4000000000000000 : ℚ) else
  if p = (3, 3) then (-1660770760339987 /
    360000000000000000 : ℚ) else
  if p = (0, 1) then (-23687367295127538706744573386260539938260889 /
    20282409603651670423947251286016000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf255_polynomial_eq :
    lowerPullbackPolynomial 5 0 majorizationTriangle255 radialPowerData5.radius
      (certifiedRadialHeight radialPowerData5 radialPowerData32)
      (certifiedRadialSlope radialPowerData5) 1 =
        planeArrayPolynomial majorizationArray255 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 5 0 majorizationTriangle255
    cellMatrix_5_0 cellMatrix_5_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf255_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray255 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf255_kernel {p : ℝ × ℝ} (hp : majorizationTriangle255.Contains p) :
    (1 : ℝ) ≤ kernel (((5 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 5 0 majorizationTriangle255
    radialPowerData5 radialPowerData32 radialPowerData5_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray255
    majorizationLeaf255_polynomial_eq majorizationLeaf255_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 256. -/
def majorizationTriangle256 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 256. -/
def majorizationArray256 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (172983238686141609779331930480325420824381888529 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (142892745161830885518065602188180389330738497629 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (3394713938740129 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (-75825506778068557 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (86583171778709196879392274602501194048732153949 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (10339977663186881 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (2136769884812919 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-14613517432812719 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-41661577309446829 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (3733384312111101 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (374794424764907 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-896594632328183 /
    120000000000000000 : ℚ) else
  if p = (3, 0) then (-37342816282847461 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (1272545839789793 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (194112460275097 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (-1660770760339987 /
    360000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf256_polynomial_eq :
    lowerPullbackPolynomial 5 0 majorizationTriangle256 radialPowerData6.radius
      (certifiedRadialHeight radialPowerData6 radialPowerData32)
      (certifiedRadialSlope radialPowerData6) 1 =
        planeArrayPolynomial majorizationArray256 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 5 0 majorizationTriangle256
    cellMatrix_5_0 cellMatrix_5_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf256_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray256 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf256_kernel {p : ℝ × ℝ} (hp : majorizationTriangle256.Contains p) :
    (1 : ℝ) ≤ kernel (((5 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 5 0 majorizationTriangle256
    radialPowerData6 radialPowerData32 radialPowerData6_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray256
    majorizationLeaf256_polynomial_eq majorizationLeaf256_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 257. -/
def majorizationTriangle257 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 257. -/
def majorizationArray257 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (4110304186029034187395146918286654552453489650841 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-467169507206607792712862105186619542056072173847 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (3184853115476201 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (451650694443389 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (-54716027936893740032528862108096677809848600669 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (755296108948689 /
    6250000000000000 : ℚ) else
  if p = (1, 2) then (-1928460517859109 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (147760096722219 /
    50000000000000000 : ℚ) else
  if p = (2, 0) then (-7900439359229429 /
    60000000000000000 : ℚ) else
  if p = (2, 1) then (-5048056755530033 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (168169590767549 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (-592834546136861 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (37342816282847461 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (1272545839789793 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (-194112460275097 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (299943367527619 /
    225000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf257_polynomial_eq :
    lowerPullbackPolynomial 5 1 majorizationTriangle257 radialPowerData6.radius
      (certifiedRadialHeight radialPowerData6 radialPowerData32)
      (certifiedRadialSlope radialPowerData6) 1 =
        planeArrayPolynomial majorizationArray257 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 5 1 majorizationTriangle257
    cellMatrix_5_1 cellMatrix_5_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf257_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray257 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf257_kernel {p : ℝ × ℝ} (hp : majorizationTriangle257.Contains p) :
    (1 : ℝ) ≤ kernel (((5 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 5 1 majorizationTriangle257
    radialPowerData6 radialPowerData32 radialPowerData6_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray257
    majorizationLeaf257_polynomial_eq majorizationLeaf257_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 258. -/
def majorizationTriangle258 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 258. -/
def majorizationArray258 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (118953181884961155318800734081571812807431820549 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (74441464670686911977726887316152032831256444493 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (21191671117826261 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-87877113002617 /
    37500000000000000 : ℚ) else
  if p = (1, 0) then (35007153063620199790293156342821732944765042253 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (1099285925070747 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (2706778153020227 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-142502067051827 /
    150000000000000000 : ℚ) else
  if p = (2, 0) then (-51709138215811903 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (2955586706907779 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (80600636087683 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (-2350729639459 /
    50000000000000000 : ℚ) else
  if p = (3, 0) then (-6213207101754317 /
    200000000000000000 : ℚ) else
  if p = (3, 1) then (6821151536418947 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-476328212948489 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (299943367527619 /
    225000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf258_polynomial_eq :
    lowerPullbackPolynomial 5 1 majorizationTriangle258 radialPowerData7.radius
      (certifiedRadialHeight radialPowerData7 radialPowerData32)
      (certifiedRadialSlope radialPowerData7) 1 =
        planeArrayPolynomial majorizationArray258 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 5 1 majorizationTriangle258
    cellMatrix_5_1 cellMatrix_5_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf258_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray258 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf258_kernel {p : ℝ × ℝ} (hp : majorizationTriangle258.Contains p) :
    (1 : ℝ) ≤ kernel (((5 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 5 1 majorizationTriangle258
    radialPowerData7 radialPowerData32 radialPowerData7_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray258
    majorizationLeaf258_polynomial_eq majorizationLeaf258_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 259. -/
def majorizationTriangle259 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 259. -/
def majorizationArray259 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (642563814917550519771823676595107739953218601 /
    348170636049013202315378688000000000000000000 : ℚ) else
  if p = (0, 1) then (-80814815853433709785926235995909626316251250253 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (363650380991959 /
    7500000000000000 : ℚ) else
  if p = (0, 3) then (-4396753248631727 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-1149060312870937127668990061701374265260261231 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (1, 1) then (227859432194853 /
    2500000000000000 : ℚ) else
  if p = (1, 2) then (-208379987505159 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (12981444951183649 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-26907000532900189 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-4888369121663363 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-256495364601763 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-15276465740134631 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (6213207101754317 /
    200000000000000000 : ℚ) else
  if p = (3, 1) then (6821151536418947 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (476328212948489 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (5295346780419869 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf259_polynomial_eq :
    lowerPullbackPolynomial 5 2 majorizationTriangle259 radialPowerData7.radius
      (certifiedRadialHeight radialPowerData7 radialPowerData32)
      (certifiedRadialSlope radialPowerData7) 1 =
        planeArrayPolynomial majorizationArray259 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 5 2 majorizationTriangle259
    cellMatrix_5_2 cellMatrix_5_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf259_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray259 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf259_kernel {p : ℝ × ℝ} (hp : majorizationTriangle259.Contains p) :
    (1 : ℝ) ≤ kernel (((5 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 5 2 majorizationTriangle259
    radialPowerData7 radialPowerData32 radialPowerData7_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray259
    majorizationLeaf259_polynomial_eq majorizationLeaf259_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 260. -/
def majorizationTriangle260 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 260. -/
def majorizationArray260 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (13725550470047875586219058515086609719944443439 /
    11884224377139650639031592550400000000000000000 : ℚ) else
  if p = (0, 1) then (32206417648440659407091443448599651310873285217 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (0, 2) then (1719726389573413 /
    40000000000000000 : ℚ) else
  if p = (0, 3) then (-2302112362887467 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (33716712307305506161973387956076708927947487011 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-64102914740509 /
    8000000000000000 : ℚ) else
  if p = (1, 2) then (4392224340846233 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-280907697971001 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-19585771398031673 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (1540005744905973 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (1012577781563391 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-38098412570311 /
    37500000000000000 : ℚ) else
  if p = (3, 0) then (-16092552130473617 /
    300000000000000000 : ℚ) else
  if p = (3, 1) then (1597822572210593 /
    37500000000000000 : ℚ) else
  if p = (3, 2) then (-2885837496684179 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (5295346780419869 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf260_polynomial_eq :
    lowerPullbackPolynomial 5 2 majorizationTriangle260 radialPowerData8.radius
      (certifiedRadialHeight radialPowerData8 radialPowerData32)
      (certifiedRadialSlope radialPowerData8) 1 =
        planeArrayPolynomial majorizationArray260 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 5 2 majorizationTriangle260
    cellMatrix_5_2 cellMatrix_5_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf260_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray260 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf260_kernel {p : ℝ × ℝ} (hp : majorizationTriangle260.Contains p) :
    (1 : ℝ) ≤ kernel (((5 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 5 2 majorizationTriangle260
    radialPowerData8 radialPowerData32 radialPowerData8_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (1 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray260
    majorizationLeaf260_polynomial_eq majorizationLeaf260_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
