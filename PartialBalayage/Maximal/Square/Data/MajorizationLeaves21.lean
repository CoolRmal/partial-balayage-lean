/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices21

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

/-- The actual closed rational triangle of majorization leaf 644. -/
def majorizationTriangle644 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 644. -/
def majorizationArray644 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1219692353574075505341323983467815628381632083063 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-25472820319880482133343837427408168876398114207 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-3052110453297277 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-34353302576759 /
    90000000000000000 : ℚ) else
  if p = (1, 0) then (-73898828874700614449519388843882127603382968541 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-923720749148631 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (147669000153473 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-81194964594591 /
    25000000000000000 : ℚ) else
  if p = (2, 0) then (-2916696676433593 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-27479029938231 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (434638462630313 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-1556875288371641 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (-206479555580969 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-2058714897274637 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-2968610222509117 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (1563205387018211 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf644_polynomial_eq :
    lowerPullbackPolynomial 15 7 majorizationTriangle644 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray644 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 7 majorizationTriangle644
    cellMatrix_15_7 cellMatrix_15_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf644_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray644 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf644_kernel {p : ℝ × ℝ} (hp : majorizationTriangle644.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 7 majorizationTriangle644
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray644
    majorizationLeaf644_polynomial_eq majorizationLeaf644_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 645. -/
def majorizationTriangle645 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 645. -/
def majorizationArray645 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5955247595305401521166971778939476094186377057 /
    23768448754279301278063185100800000000000000000 : ℚ) else
  if p = (0, 1) then (23861314188417000725276156013138090428186261603 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-405287002457781 /
    40000000000000000 : ℚ) else
  if p = (0, 3) then (1805506749411679 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (7832917814050636421398216920398913264406243361 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (1, 1) then (-209610824216523 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-3941003882312133 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (5892668179407151 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-2284831203064279 /
    200000000000000000 : ℚ) else
  if p = (2, 1) then (-3800960459450141 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (8421126146541813 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-10955097906420617 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (127845290880763 /
    112500000000000000 : ℚ) else
  if p = (3, 1) then (1518228285217757 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (-5550119130327391 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (1563205387018211 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf645_polynomial_eq :
    lowerPullbackPolynomial 15 7 majorizationTriangle645 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray645 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 7 majorizationTriangle645
    cellMatrix_15_7 cellMatrix_15_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf645_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray645 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf645_kernel {p : ℝ × ℝ} (hp : majorizationTriangle645.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 7 majorizationTriangle645
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray645
    majorizationLeaf645_polynomial_eq majorizationLeaf645_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 646. -/
def majorizationTriangle646 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 646. -/
def majorizationArray646 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (241817969979892786507546618400594053066206262919 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 1) then (-6834788402136469827430294089614852169324832801 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (0, 2) then (-3739176504832457 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-54627883472123 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (-18878379904537504316879806706552548841052207203 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-2577061899111869 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-1801010150116711 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (2803239777678173 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-4808968955100629 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-2271952681420887 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-2679112114112969 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (889035373777913 /
    50000000000000000 : ℚ) else
  if p = (3, 0) then (-127845290880763 /
    112500000000000000 : ℚ) else
  if p = (3, 1) then (1518228285217757 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (5550119130327391 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-7191425152978237 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf646_polynomial_eq :
    lowerPullbackPolynomial 15 8 majorizationTriangle646 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray646 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 8 majorizationTriangle646
    cellMatrix_15_8 cellMatrix_15_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf646_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray646 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf646_kernel {p : ℝ × ℝ} (hp : majorizationTriangle646.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 8 majorizationTriangle646
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray646
    majorizationLeaf646_polynomial_eq majorizationLeaf646_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 647. -/
def majorizationTriangle647 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 647. -/
def majorizationArray647 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5456813287954213988201443776608466836954063597 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (79967288088741396335839323399561213068558238169 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (12996404570796029 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-2384463700957843 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (26204368343218343275696809081360826718671525363 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (5011581557654961 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-2118631796425443 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-60745736196223 /
    20000000000000000 : ℚ) else
  if p = (2, 0) then (11714490082205033 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-101837465038231 /
    8000000000000000 : ℚ) else
  if p = (2, 2) then (-9676149980036179 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (2262159515822249 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (-10354114469286137 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-123077737433089 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (8832731175629083 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-7191425152978237 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf647_polynomial_eq :
    lowerPullbackPolynomial 15 8 majorizationTriangle647 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray647 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 8 majorizationTriangle647
    cellMatrix_15_8 cellMatrix_15_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf647_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray647 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf647_kernel {p : ℝ × ℝ} (hp : majorizationTriangle647.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 8 majorizationTriangle647
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray647
    majorizationLeaf647_polynomial_eq majorizationLeaf647_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 648. -/
def majorizationTriangle648 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 648. -/
def majorizationArray648 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (695257931011026981563811910186148211407591600027 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-90908101291150575963600280242826789061970395609 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-4722478407330671 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (5972022353531101 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-27641435811762079923767467767288703617604179443 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-114520528797789 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (761093881047927 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-2738631350341459 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-8993738856367241 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (3038247575688131 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (7989312371221987 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-5395454593400189 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (10354114469286137 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (-123077737433089 /
    150000000000000000 : ℚ) else
  if p = (3, 2) then (-8832731175629083 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (7356905109319237 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf648_polynomial_eq :
    lowerPullbackPolynomial 15 9 majorizationTriangle648 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray648 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 9 majorizationTriangle648
    cellMatrix_15_9 cellMatrix_15_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf648_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray648 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf648_kernel {p : ℝ × ℝ} (hp : majorizationTriangle648.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 9 majorizationTriangle648
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray648
    majorizationLeaf648_polynomial_eq majorizationLeaf648_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 649. -/
def majorizationTriangle649 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 649. -/
def majorizationArray649 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (693238039827204056975517336102261047831260353 /
    7922816251426433759354395033600000000000000000 : ℚ) else
  if p = (0, 1) then (8291706817469664464976916730195131312004073069 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (594184446173367 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (9431297893755827 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (8291706817469664464976916730195131312004073069 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (1782553338520101 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (1782553338520101 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-378915898231043 /
    40000000000000000 : ℚ) else
  if p = (2, 0) then (594184446173367 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (1782553338520101 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (1782553338520101 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-13241256657076381 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (542183815890293 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (-319780760748587 /
    30000000000000000 : ℚ) else
  if p = (3, 2) then (-5881079043009391 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (7356905109319237 /
    450000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf649_polynomial_eq :
    lowerPullbackPolynomial 15 9 majorizationTriangle649 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray649 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 9 majorizationTriangle649
    cellMatrix_15_9 cellMatrix_15_9_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf649_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray649 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf649_kernel {p : ℝ × ℝ} (hp : majorizationTriangle649.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((9 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 9 majorizationTriangle649
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray649
    majorizationLeaf649_polynomial_eq majorizationLeaf649_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 650. -/
def majorizationTriangle650 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 650. -/
def majorizationArray650 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (211318412260037420006137295662037102719884833161 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-36755403107457968450433065807134008675781645127 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (1649198581657829 /
    75000000000000000 : ℚ) else
  if p = (0, 3) then (-10510317217739111 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-33960755674430402677811433739101669764599452487 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (2149852408074433 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (2083668075973 /
    390625000000000 : ℚ) else
  if p = (1, 3) then (-3750109490421697 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (3951288602081273 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (1415254268965769 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-409852570448929 /
    10000000000000000 : ℚ) else
  if p = (2, 3) then (10880322844502101 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-542183815890293 /
    225000000000000000 : ℚ) else
  if p = (3, 1) then (-319780760748587 /
    30000000000000000 : ℚ) else
  if p = (3, 2) then (5881079043009391 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-14445429521542303 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf650_polynomial_eq :
    lowerPullbackPolynomial 15 10 majorizationTriangle650 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray650 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 10 majorizationTriangle650
    cellMatrix_15_10 cellMatrix_15_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf650_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray650 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf650_kernel {p : ℝ × ℝ} (hp : majorizationTriangle650.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 10 majorizationTriangle650
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray650
    majorizationLeaf650_polynomial_eq majorizationLeaf650_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 651. -/
def majorizationTriangle651 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 651. -/
def majorizationArray651 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (32497214358872138161475135455980843945112687 /
    792281625142643375935439503360000000000000000 : ℚ) else
  if p = (0, 1) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 3) then (198061482057789 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 3) then (594184446173367 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (594184446173367 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (2683271435523521 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (2683271435523521 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (2683271435523521 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-14445429521542303 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf651_polynomial_eq :
    lowerPullbackPolynomial 15 10 majorizationTriangle651 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray651 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 10 majorizationTriangle651
    cellMatrix_15_10 cellMatrix_15_10_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf651_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray651 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf651_kernel {p : ℝ × ℝ} (hp : majorizationTriangle651.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((10 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 10 majorizationTriangle651
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray651
    majorizationLeaf651_polynomial_eq majorizationLeaf651_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 652. -/
def majorizationTriangle652 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 652. -/
def majorizationArray652 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (243003792405659445816457838932886751312576252337 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-44839149109420461264670227798918000031174900459 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (2683271435523521 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-2683271435523521 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-44839149109420461264670227798918000031174900459 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (2683271435523521 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-2683271435523521 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (2683271435523521 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (2683271435523521 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-2683271435523521 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (2683271435523521 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-2683271435523521 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-2683271435523521 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (2683271435523521 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-2683271435523521 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (2683271435523521 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf652_polynomial_eq :
    lowerPullbackPolynomial 15 11 majorizationTriangle652 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray652 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 11 majorizationTriangle652
    cellMatrix_15_11 cellMatrix_15_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf652_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray652 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf652_kernel {p : ℝ × ℝ} (hp : majorizationTriangle652.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 11 majorizationTriangle652
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray652
    majorizationLeaf652_polynomial_eq majorizationLeaf652_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 653. -/
def majorizationTriangle653 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 653. -/
def majorizationArray653 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 1) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (3, 3) then (2683271435523521 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf653_polynomial_eq :
    lowerPullbackPolynomial 15 11 majorizationTriangle653 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray653 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 11 majorizationTriangle653
    cellMatrix_15_11 cellMatrix_15_11_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf653_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray653 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf653_kernel {p : ℝ × ℝ} (hp : majorizationTriangle653.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((11 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 11 majorizationTriangle653
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray653
    majorizationLeaf653_polynomial_eq majorizationLeaf653_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 654. -/
def majorizationTriangle654 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 654. -/
def majorizationArray654 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 0) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 1) then (-12488834261681720212487106810607059626855304549 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf654_polynomial_eq :
    lowerPullbackPolynomial 15 12 majorizationTriangle654 radialPowerData32.radius
      (certifiedRadialHeight radialPowerData32 radialPowerData32)
      (certifiedRadialSlope radialPowerData32) 0 =
        planeArrayPolynomial majorizationArray654 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 15 12 majorizationTriangle654
    cellMatrix_15_12 cellMatrix_15_12_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf654_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray654 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf654_kernel {p : ℝ × ℝ} (hp : majorizationTriangle654.Contains p) :
    (0 : ℝ) ≤ kernel (((15 : ℝ) + p.1) / 16) (((12 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 15 12 majorizationTriangle654
    radialPowerData32 radialPowerData32 radialPowerData32_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray654
    majorizationLeaf654_polynomial_eq majorizationLeaf654_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
