/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices29

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

/-- The actual closed rational triangle of majorization leaf 735. -/
def majorizationTriangle735 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 735. -/
def majorizationArray735 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (96933992627668311000050750173743336445576611233 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 2) then (-220687356518999 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (71335295606279 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-5142736283511486824599370447371103033599270691 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 2) then (-29647870860637 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (-220584582182593 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-357979716902251 /
    300000000000000000 : ℚ) else
  if p = (2, 2) then (26509964861413 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-110310174544463 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (38973267007007 /
    225000000000000000 : ℚ) else
  if p = (3, 2) then (-61655354448953 /
    60000000000000000 : ℚ) else
  if p = (3, 3) then (1384703961180463 /
    1800000000000000000 : ℚ) else
  if p = (0, 1) then (-1469830110764502104921594408742724447131077217 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf735_polynomial_eq :
    lowerPullbackPolynomial 20 0 majorizationTriangle735 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray735 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 0 majorizationTriangle735
    cellMatrix_20_0 cellMatrix_20_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf735_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray735 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf735_kernel {p : ℝ × ℝ} (hp : majorizationTriangle735.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 0 majorizationTriangle735
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray735
    majorizationLeaf735_polynomial_eq majorizationLeaf735_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 736. -/
def majorizationTriangle736 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 736. -/
def majorizationArray736 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (91056943008673219834906270193380636754819777 /
    237684487542793012780631851008000000000000000 : ℚ) else
  if p = (0, 1) then (68647775108281828753090889939922619945083234383 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-26546555200081 /
    10000000000000000 : ℚ) else
  if p = (0, 3) then (27917734724323 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (78885972931579264078410509202855609087210317903 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-67984035793807 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (10403488654841 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (41854860977591 /
    50000000000000000 : ℚ) else
  if p = (2, 0) then (-146990152555501 /
    100000000000000000 : ℚ) else
  if p = (2, 1) then (-16373033729659 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (135814938125799 /
    50000000000000000 : ℚ) else
  if p = (2, 3) then (-526886718773537 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (153170536232071 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (50532290733801 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-768150416690933 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (1384703961180463 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf736_polynomial_eq :
    lowerPullbackPolynomial 20 0 majorizationTriangle736 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray736 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 0 majorizationTriangle736
    cellMatrix_20_0 cellMatrix_20_0_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf736_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray736 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf736_kernel {p : ℝ × ℝ} (hp : majorizationTriangle736.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((0 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 0 majorizationTriangle736
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray736
    majorizationLeaf736_polynomial_eq majorizationLeaf736_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 737. -/
def majorizationTriangle737 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 737. -/
def majorizationArray737 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1325391469811477314320740838671775019433421393869 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-66146925182169466279295691805738935042670618703 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-668743539257159 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-1138211208429869 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-76333699007599797023751461138630602084475234383 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-457767549067689 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-339176065625141 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (301859299941703 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-145754075820187 /
    120000000000000000 : ℚ) else
  if p = (2, 1) then (-23770160948417 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (-224890664187737 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (24809711833111 /
    24000000000000000 : ℚ) else
  if p = (3, 0) then (-153170536232071 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (50532290733801 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (768150416690933 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-3169293208701107 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf737_polynomial_eq :
    lowerPullbackPolynomial 20 1 majorizationTriangle737 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray737 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 1 majorizationTriangle737
    cellMatrix_20_1 cellMatrix_20_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf737_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray737 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf737_kernel {p : ℝ × ℝ} (hp : majorizationTriangle737.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 1 majorizationTriangle737
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray737
    majorizationLeaf737_polynomial_eq majorizationLeaf737_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 738. -/
def majorizationTriangle738 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 738. -/
def majorizationArray738 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5536483826170570750881198255091877671074653827 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (70204177862330563281386238294553258186818805981 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-1566995720913701 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (770599064911271 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (26071599604758300941218477285400473054264456607 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-1106217279036837 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (51492352950423 /
    6250000000000000 : ℚ) else
  if p = (1, 3) then (-813474158551927 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-425743467079699 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (714892420203811 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (-250723832546267 /
    25000000000000000 : ℚ) else
  if p = (2, 3) then (637262603218333 /
    150000000000000000 : ℚ) else
  if p = (3, 0) then (6258020869513 /
    20000000000000000 : ℚ) else
  if p = (3, 1) then (-740697751558919 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (400190465335029 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (-3169293208701107 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf738_polynomial_eq :
    lowerPullbackPolynomial 20 1 majorizationTriangle738 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray738 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 1 majorizationTriangle738
    cellMatrix_20_1 cellMatrix_20_1_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf738_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray738 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf738_kernel {p : ℝ × ℝ} (hp : majorizationTriangle738.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((1 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 1 majorizationTriangle738
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray738
    majorizationLeaf738_polynomial_eq majorizationLeaf738_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 739. -/
def majorizationTriangle739 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 739. -/
def majorizationArray739 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1113278859896354991492158868776256905545277256823 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-64136339047572810153028298216650927358993326301 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-451738686921757 /
    150000000000000000 : ℚ) else
  if p = (0, 3) then (-1620221927922193 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-73710319888448005013116939583137024984532213981 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-208565095094067 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (-18658382841719 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-562138645533729 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-569875995031313 /
    300000000000000000 : ℚ) else
  if p = (2, 1) then (6451332838777 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (197676065820019 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-2419594887585229 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-6258020869513 /
    20000000000000000 : ℚ) else
  if p = (3, 1) then (-740697751558919 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-400190465335029 /
    100000000000000000 : ℚ) else
  if p = (3, 3) then (10860703985232343 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf739_polynomial_eq :
    lowerPullbackPolynomial 20 2 majorizationTriangle739 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray739 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 2 majorizationTriangle739
    cellMatrix_20_2 cellMatrix_20_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf739_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray739 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf739_kernel {p : ℝ × ℝ} (hp : majorizationTriangle739.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 2 majorizationTriangle739
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray739
    majorizationLeaf739_polynomial_eq majorizationLeaf739_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 740. -/
def majorizationTriangle740 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 740. -/
def majorizationArray740 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (16584233723640628522950415950294045681553370659 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (19962635653023292653670448954331686913299216483 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-12423083714153 /
    1200000000000000 : ℚ) else
  if p = (0, 3) then (512925069208183 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (21133370617975547927034851891458834569598367843 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-73302929590003 /
    12500000000000000 : ℚ) else
  if p = (1, 2) then (-1343671489523581 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (2167549136730349 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-892147818251239 /
    150000000000000000 : ℚ) else
  if p = (2, 1) then (-149987146824961 /
    10000000000000000 : ℚ) else
  if p = (2, 2) then (3217659218638489 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-1406851516274519 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (1350132778407863 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (1525674299364719 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-8459561193222169 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (10860703985232343 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf740_polynomial_eq :
    lowerPullbackPolynomial 20 2 majorizationTriangle740 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray740 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 2 majorizationTriangle740
    cellMatrix_20_2 cellMatrix_20_2_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf740_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray740 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf740_kernel {p : ℝ × ℝ} (hp : majorizationTriangle740.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((2 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 2 majorizationTriangle740
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray740
    majorizationLeaf740_polynomial_eq majorizationLeaf740_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 741. -/
def majorizationTriangle741 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 741. -/
def majorizationArray741 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (225536297846381264445680986952076097849260291719 /
    713053462628379038341895553024000000000000000000 : ℚ) else
  if p = (0, 1) then (-16816981869523382659260914670665768996075239523 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-3427176675609221 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-36875830144293 /
    20000000000000000 : ℚ) else
  if p = (1, 0) then (-18840884020646993901731460948058515002259175523 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (1, 1) then (-2595309848344331 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-13789861618277 /
    1600000000000000 : ℚ) else
  if p = (1, 3) then (79544257240361 /
    10000000000000000 : ℚ) else
  if p = (2, 0) then (-2218458494597093 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-1577279961594937 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-2024242755945191 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (1506004576929153 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-1350132778407863 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (1525674299364719 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (8459561193222169 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (-4647817797516221 /
    360000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf741_polynomial_eq :
    lowerPullbackPolynomial 20 3 majorizationTriangle741 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray741 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 3 majorizationTriangle741
    cellMatrix_20_3 cellMatrix_20_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf741_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray741 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf741_kernel {p : ℝ × ℝ} (hp : majorizationTriangle741.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 3 majorizationTriangle741
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray741
    majorizationLeaf741_polynomial_eq majorizationLeaf741_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 742. -/
def majorizationTriangle742 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 742. -/
def majorizationArray742 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (5309663275463192578257188840600067549524173549 /
    35652673131418951917094777651200000000000000000 : ℚ) else
  if p = (0, 1) then (71458817274510724067888766318014436358990627289 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (8656593130345759 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-14868134987422259 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (73441568795880893257068102559982324230535807449 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (3807460454644667 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-2292964349037553 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-394378630009609 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (10533531322317451 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-1667318285046989 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-7767743088729209 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (14203061526006187 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (-484017683598667 /
    60000000000000000 : ℚ) else
  if p = (3, 1) then (-174294370304261 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (615813658098289 /
    25000000000000000 : ℚ) else
  if p = (3, 3) then (-4647817797516221 /
    360000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf742_polynomial_eq :
    lowerPullbackPolynomial 20 3 majorizationTriangle742 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray742 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 3 majorizationTriangle742
    cellMatrix_20_3 cellMatrix_20_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf742_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray742 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf742_kernel {p : ℝ × ℝ} (hp : majorizationTriangle742.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 3 majorizationTriangle742
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray742
    majorizationLeaf742_polynomial_eq majorizationLeaf742_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 743. -/
def majorizationTriangle743 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 743. -/
def majorizationArray743 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (672162209294357950606938580896181788777466851227 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-78870584632344158486791190477668668316329476569 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-6746001388595591 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (2743059959078051 /
    300000000000000000 : ℚ) else
  if p = (1, 0) then (-83814963036467543207277407846586205459059081689 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-1270119818491921 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (609784546427407 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (-18681049688177 /
    20000000000000000 : ℚ) else
  if p = (2, 0) then (-3986999185642559 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (3410261988089599 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (7011784705629727 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-650029197950153 /
    25000000000000000 : ℚ) else
  if p = (3, 0) then (484017683598667 /
    60000000000000000 : ℚ) else
  if p = (3, 1) then (-174294370304261 /
    60000000000000000 : ℚ) else
  if p = (3, 2) then (-615813658098289 /
    25000000000000000 : ℚ) else
  if p = (3, 3) then (26418656241373991 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf743_polynomial_eq :
    lowerPullbackPolynomial 20 4 majorizationTriangle743 radialPowerData29.radius
      (certifiedRadialHeight radialPowerData29 radialPowerData32)
      (certifiedRadialSlope radialPowerData29) 0 =
        planeArrayPolynomial majorizationArray743 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 4 majorizationTriangle743
    cellMatrix_20_4 cellMatrix_20_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf743_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray743 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf743_kernel {p : ℝ × ℝ} (hp : majorizationTriangle743.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 4 majorizationTriangle743
    radialPowerData29 radialPowerData32 radialPowerData29_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray743
    majorizationLeaf743_polynomial_eq majorizationLeaf743_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 744. -/
def majorizationTriangle744 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 744. -/
def majorizationArray744 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2072915098262755836494073179558605713733731907 /
    23768448754279301278063185100800000000000000000 : ℚ) else
  if p = (0, 1) then (8155726393092537776327340155231582716803090029 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (101673746728037 /
    20000000000000000 : ℚ) else
  if p = (0, 3) then (5606380728504649 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (8155726393092537776327340155231582716803090029 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (1, 1) then (305021240184111 /
    20000000000000000 : ℚ) else
  if p = (1, 2) then (305021240184111 /
    20000000000000000 : ℚ) else
  if p = (1, 3) then (-5343176750878663 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (101673746728037 /
    20000000000000000 : ℚ) else
  if p = (2, 1) then (305021240184111 /
    20000000000000000 : ℚ) else
  if p = (2, 2) then (305021240184111 /
    20000000000000000 : ℚ) else
  if p = (2, 3) then (-10817955490570319 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (8628227742870637 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-1627781016795497 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-2327825689403011 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (26418656241373991 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf744_polynomial_eq :
    lowerPullbackPolynomial 20 4 majorizationTriangle744 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray744 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 4 majorizationTriangle744
    cellMatrix_20_4 cellMatrix_20_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf744_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray744 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf744_kernel {p : ℝ × ℝ} (hp : majorizationTriangle744.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 4 majorizationTriangle744
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray744
    majorizationLeaf744_polynomial_eq majorizationLeaf744_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 745. -/
def majorizationTriangle745 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 745. -/
def majorizationArray745 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (211862311448103340808085996050749376795351953801 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-11699319881251297374810405749353213560500979309 /
    158456325028528675187087900672000000000000000000 : ℚ) else
  if p = (0, 2) then (1942471673174543 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (-2111488555852811 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-36136419955021843743555053027376526982478369607 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (4267294155136839 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (99539649659669 /
    8000000000000000 : ℚ) else
  if p = (1, 3) then (-1955461313268669 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (11678440144711747 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (1833130648545381 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-1717783209034789 /
    40000000000000000 : ℚ) else
  if p = (2, 3) then (3988936247829409 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-8628227742870637 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (-1627781016795497 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (2327825689403011 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (-1668557905036593 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf745_polynomial_eq :
    lowerPullbackPolynomial 20 5 majorizationTriangle745 radialPowerData30.radius
      (certifiedRadialHeight radialPowerData30 radialPowerData32)
      (certifiedRadialSlope radialPowerData30) 0 =
        planeArrayPolynomial majorizationArray745 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 5 majorizationTriangle745
    cellMatrix_20_5 cellMatrix_20_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf745_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray745 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf745_kernel {p : ℝ × ℝ} (hp : majorizationTriangle745.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 5 majorizationTriangle745
    radialPowerData30 radialPowerData32 radialPowerData30_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray745
    majorizationLeaf745_polynomial_eq majorizationLeaf745_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 746. -/
def majorizationTriangle746 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 746. -/
def majorizationArray746 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (32497214358872138161475135455980843945112687 /
    792281625142643375935439503360000000000000000 : ℚ) else
  if p = (0, 1) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 3) then (101673746728037 /
    60000000000000000 : ℚ) else
  if p = (1, 0) then (13529111934049881195079520582072952179832613113 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 3) then (101673746728037 /
    20000000000000000 : ℚ) else
  if p = (2, 3) then (101673746728037 /
    20000000000000000 : ℚ) else
  if p = (3, 0) then (1688946349157141 /
    900000000000000000 : ℚ) else
  if p = (3, 1) then (1688946349157141 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (1688946349157141 /
    300000000000000000 : ℚ) else
  if p = (3, 3) then (-1668557905036593 /
    200000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf746_polynomial_eq :
    lowerPullbackPolynomial 20 5 majorizationTriangle746 radialPowerData31.radius
      (certifiedRadialHeight radialPowerData31 radialPowerData32)
      (certifiedRadialSlope radialPowerData31) 0 =
        planeArrayPolynomial majorizationArray746 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 20 5 majorizationTriangle746
    cellMatrix_20_5 cellMatrix_20_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf746_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray746 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf746_kernel {p : ℝ × ℝ} (hp : majorizationTriangle746.Contains p) :
    (0 : ℝ) ≤ kernel (((20 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 20 5 majorizationTriangle746
    radialPowerData31 radialPowerData32 radialPowerData31_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray746
    majorizationLeaf746_polynomial_eq majorizationLeaf746_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
