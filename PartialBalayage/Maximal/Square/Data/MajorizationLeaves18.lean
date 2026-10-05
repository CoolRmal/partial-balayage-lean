/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.Data.CellMatrices18

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

/-- The actual closed rational triangle of majorization leaf 609. -/
def majorizationTriangle609 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 609. -/
def majorizationArray609 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1250317681352666316926533962990536900970946973047 /
    1426106925256758076683791106048000000000000000000 : ℚ) else
  if p = (0, 1) then (-44485045998284397937750113736100647391090070409 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (0, 2) then (19178752153447 /
    37500000000000000 : ℚ) else
  if p = (0, 3) then (-702459649931099 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (-46682125923870445200432451183265827274417394569 /
    475368975085586025561263702016000000000000000000 : ℚ) else
  if p = (1, 1) then (-142751841526777 /
    50000000000000000 : ℚ) else
  if p = (1, 2) then (-64057940363521 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (2735606903337 /
    20000000000000000 : ℚ) else
  if p = (2, 0) then (-128415714897461 /
    37500000000000000 : ℚ) else
  if p = (2, 1) then (1203314109379 /
    100000000000000000 : ℚ) else
  if p = (2, 2) then (116513180153 /
    2500000000000000 : ℚ) else
  if p = (2, 3) then (-6803981460113 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (45034058365541 /
    200000000000000000 : ℚ) else
  if p = (3, 1) then (-2921902231007 /
    120000000000000000 : ℚ) else
  if p = (3, 2) then (-1078551634379 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-7103680887059 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf609_polynomial_eq :
    lowerPullbackPolynomial 14 3 majorizationTriangle609 radialPowerData17.radius
      (certifiedRadialHeight radialPowerData17 radialPowerData32)
      (certifiedRadialSlope radialPowerData17) 0 =
        planeArrayPolynomial majorizationArray609 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 3 majorizationTriangle609
    cellMatrix_14_3 cellMatrix_14_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf609_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray609 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf609_kernel {p : ℝ × ℝ} (hp : majorizationTriangle609.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 3 majorizationTriangle609
    radialPowerData17 radialPowerData32 radialPowerData17_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray609
    majorizationLeaf609_polynomial_eq majorizationLeaf609_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 610. -/
def majorizationTriangle610 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 610. -/
def majorizationArray610 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (48782373523793337730046489658172232589605157499 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (82680214773272933581422695803816406484490203943 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-253301205697811 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (151718241137083 /
    225000000000000000 : ℚ) else
  if p = (1, 0) then (30453123574963528274873347412407549255429067021 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (1, 1) then (-153115510990097 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (72064507320159 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (677415324759 /
    10000000000000000 : ℚ) else
  if p = (2, 0) then (-1695512688045373 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (5569481722483 /
    40000000000000000 : ℚ) else
  if p = (2, 2) then (-21729925185241 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (3476915586793 /
    75000000000000000 : ℚ) else
  if p = (3, 0) then (-67512733068247 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-35288182735427 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (3488603335451 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (-7103680887059 /
    900000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf610_polynomial_eq :
    lowerPullbackPolynomial 14 3 majorizationTriangle610 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray610 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 3 majorizationTriangle610
    cellMatrix_14_3 cellMatrix_14_3_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf610_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray610 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf610_kernel {p : ℝ × ℝ} (hp : majorizationTriangle610.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((3 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 3 majorizationTriangle610
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray610
    majorizationLeaf610_polynomial_eq majorizationLeaf610_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 611. -/
def majorizationTriangle611 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 611. -/
def majorizationArray611 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (738926073620022194151953133820434973562271361423 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 1) then (-26372452726732115642577460366638847008469881101 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-183009877567841 /
    100000000000000000 : ℚ) else
  if p = (0, 3) then (-1501369062104021 /
    1800000000000000000 : ℚ) else
  if p = (1, 0) then (-85451185554421023300630308069369556226565288743 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-372585460230541 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (-11511918406733 /
    50000000000000000 : ℚ) else
  if p = (1, 3) then (31018930612903 /
    200000000000000000 : ℚ) else
  if p = (2, 0) then (-42355757362221 /
    12500000000000000 : ℚ) else
  if p = (2, 1) then (1860193530753 /
    50000000000000000 : ℚ) else
  if p = (2, 2) then (-2143454253993 /
    100000000000000000 : ℚ) else
  if p = (2, 3) then (-44287968784043 /
    600000000000000000 : ℚ) else
  if p = (3, 0) then (67512733068247 /
    360000000000000000 : ℚ) else
  if p = (3, 1) then (-35288182735427 /
    600000000000000000 : ℚ) else
  if p = (3, 2) then (-3488603335451 /
    120000000000000000 : ℚ) else
  if p = (3, 3) then (67061911350583 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf611_polynomial_eq :
    lowerPullbackPolynomial 14 4 majorizationTriangle611 radialPowerData18.radius
      (certifiedRadialHeight radialPowerData18 radialPowerData32)
      (certifiedRadialSlope radialPowerData18) 0 =
        planeArrayPolynomial majorizationArray611 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 4 majorizationTriangle611
    cellMatrix_14_4 cellMatrix_14_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf611_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray611 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf611_kernel {p : ℝ × ℝ} (hp : majorizationTriangle611.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 4 majorizationTriangle611
    radialPowerData18 radialPowerData32 radialPowerData18_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray611
    majorizationLeaf611_polynomial_eq majorizationLeaf611_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 612. -/
def majorizationTriangle612 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 612. -/
def majorizationArray612 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (8548261292558015164023921441736245252646151839 /
    14261069252567580766837911060480000000000000000 : ℚ) else
  if p = (0, 1) then (9918979142346239643493430685312888787869592097 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (-510901342015699 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (4025002129967 /
    5625000000000000 : ℚ) else
  if p = (1, 0) then (3576869965627336529678604989362150310986894859 /
    39614081257132168796771975168000000000000000000 : ℚ) else
  if p = (1, 1) then (-838163803969597 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (521741698953 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (11923794270201 /
    100000000000000000 : ℚ) else
  if p = (2, 0) then (-1821470746871801 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (48533316416357 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (1044017381299 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-1138697128327 /
    30000000000000000 : ℚ) else
  if p = (3, 0) then (-6845332734827 /
    50000000000000000 : ℚ) else
  if p = (3, 1) then (-518717456559 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (-1033726972361 /
    12500000000000000 : ℚ) else
  if p = (3, 3) then (67061911350583 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf612_polynomial_eq :
    lowerPullbackPolynomial 14 4 majorizationTriangle612 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray612 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 4 majorizationTriangle612
    cellMatrix_14_4 cellMatrix_14_4_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf612_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray612 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf612_kernel {p : ℝ × ℝ} (hp : majorizationTriangle612.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((4 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 4 majorizationTriangle612
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray612
    majorizationLeaf612_polynomial_eq majorizationLeaf612_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 613. -/
def majorizationTriangle613 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 613. -/
def majorizationArray613 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (122383606384945629426945391628767989419582308853 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-9449155392426386894161271956968241602498619937 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (0, 2) then (-2599428327511067 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (-99745138446493 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-9960240113047204300085633547408670857346640417 /
    118842243771396506390315925504000000000000000000 : ℚ) else
  if p = (1, 1) then (-744209475876237 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (47009118211777 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (9087194638601 /
    120000000000000000 : ℚ) else
  if p = (2, 0) then (-2067902725325573 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-45421011677003 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-48574877292029 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (15697260279071 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (6845332734827 /
    50000000000000000 : ℚ) else
  if p = (3, 1) then (-518717456559 /
    100000000000000000 : ℚ) else
  if p = (3, 2) then (1033726972361 /
    12500000000000000 : ℚ) else
  if p = (3, 3) then (-17029992999017 /
    120000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf613_polynomial_eq :
    lowerPullbackPolynomial 14 5 majorizationTriangle613 radialPowerData19.radius
      (certifiedRadialHeight radialPowerData19 radialPowerData32)
      (certifiedRadialSlope radialPowerData19) 0 =
        planeArrayPolynomial majorizationArray613 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 5 majorizationTriangle613
    cellMatrix_14_5 cellMatrix_14_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf613_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray613 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf613_kernel {p : ℝ × ℝ} (hp : majorizationTriangle613.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 5 majorizationTriangle613
    radialPowerData19 radialPowerData32 radialPowerData19_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray613
    majorizationLeaf613_polynomial_eq majorizationLeaf613_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 614. -/
def majorizationTriangle614 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 614. -/
def majorizationArray614 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (2298933971539681315089955468175520601314765467 /
    4456584141427368989636847206400000000000000000 : ℚ) else
  if p = (0, 1) then (1664420442734985511993891719864123705614338657 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (0, 2) then (-113264350332503 /
    24000000000000000 : ℚ) else
  if p = (0, 3) then (577295933821 /
    3750000000000000 : ℚ) else
  if p = (1, 0) then (5126311129319087856757540484119273185400921891 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 1) then (-955037647485327 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (116352101816777 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-1809849376841 /
    9375000000000000 : ℚ) else
  if p = (2, 0) then (-2172296758125017 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (254803395801801 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-207314096766743 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (34726352358007 /
    100000000000000000 : ℚ) else
  if p = (3, 0) then (-43500617756813 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-53108136792651 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (68610333437309 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (-17029992999017 /
    120000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf614_polynomial_eq :
    lowerPullbackPolynomial 14 5 majorizationTriangle614 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray614 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 5 majorizationTriangle614
    cellMatrix_14_5 cellMatrix_14_5_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf614_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray614 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf614_kernel {p : ℝ × ℝ} (hp : majorizationTriangle614.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((5 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 5 majorizationTriangle614
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray614
    majorizationLeaf614_polynomial_eq majorizationLeaf614_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 615. -/
def majorizationTriangle615 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 615. -/
def majorizationArray615 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (106677966419813093336948931843422065997325403553 /
    178263365657094759585473888256000000000000000000 : ℚ) else
  if p = (0, 1) then (-1589813026256142250884499941849927930605406817 /
    19807040628566084398385987584000000000000000000 : ℚ) else
  if p = (0, 2) then (-1449331871425273 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (130546463341 /
    450000000000000000 : ℚ) else
  if p = (1, 0) then (-4683119150315088040463780685335617942341885731 /
    59421121885698253195157962752000000000000000000 : ℚ) else
  if p = (1, 1) then (-302377633129839 /
    100000000000000000 : ℚ) else
  if p = (1, 2) then (46222545702391 /
    100000000000000000 : ℚ) else
  if p = (1, 3) then (-10711352538151 /
    60000000000000000 : ℚ) else
  if p = (2, 0) then (-17990614151527 /
    4687500000000000 : ℚ) else
  if p = (2, 1) then (-11934873177981 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (-46346764213 /
    6250000000000000 : ℚ) else
  if p = (2, 3) then (-16926120752831 /
    37500000000000000 : ℚ) else
  if p = (3, 0) then (43500617756813 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (-53108136792651 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-68610333437309 /
    200000000000000000 : ℚ) else
  if p = (3, 3) then (19016051905049 /
    37500000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf615_polynomial_eq :
    lowerPullbackPolynomial 14 6 majorizationTriangle615 radialPowerData20.radius
      (certifiedRadialHeight radialPowerData20 radialPowerData32)
      (certifiedRadialSlope radialPowerData20) 0 =
        planeArrayPolynomial majorizationArray615 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 6 majorizationTriangle615
    cellMatrix_14_6 cellMatrix_14_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf615_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray615 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf615_kernel {p : ℝ × ℝ} (hp : majorizationTriangle615.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 6 majorizationTriangle615
    radialPowerData20 radialPowerData32 radialPowerData20_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray615
    majorizationLeaf615_polynomial_eq majorizationLeaf615_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 616. -/
def majorizationTriangle616 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 616. -/
def majorizationArray616 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (7677385131138942636030252880622869000415983243 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (27450649206174699990173754121317103477169857221 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-3052110453297277 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (110250847492351 /
    900000000000000000 : ℚ) else
  if p = (1, 0) then (79832315533583268020009138925608931405698197583 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-923720749148631 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (-147669000153473 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (1056084407881 /
    2400000000000000 : ℚ) else
  if p = (2, 0) then (-2916696676433593 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (27479029938231 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (434638462630313 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-10030508740579 /
    9375000000000000 : ℚ) else
  if p = (3, 0) then (17397962452283 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (22785605362703 /
    40000000000000000 : ℚ) else
  if p = (3, 2) then (-9425859881739 /
    8000000000000000 : ℚ) else
  if p = (3, 3) then (19016051905049 /
    37500000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf616_polynomial_eq :
    lowerPullbackPolynomial 14 6 majorizationTriangle616 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray616 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 6 majorizationTriangle616
    cellMatrix_14_6 cellMatrix_14_6_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf616_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray616 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf616_kernel {p : ℝ × ℝ} (hp : majorizationTriangle616.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((6 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 6 majorizationTriangle616
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray616
    majorizationLeaf616_polynomial_eq majorizationLeaf616_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 617. -/
def majorizationTriangle617 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 617. -/
def majorizationArray617 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1454096201001658096247849943909964554395318702029 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-26211023679007607872449482825768413652347790021 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-1449070778498591 /
    300000000000000000 : ℚ) else
  if p = (0, 3) then (-113395859962151 /
    600000000000000000 : ℚ) else
  if p = (1, 0) then (-70671639317966645897260783077790007221245732943 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-65872326103953 /
    25000000000000000 : ℚ) else
  if p = (1, 2) then (-1833554247091 /
    25000000000000000 : ℚ) else
  if p = (1, 3) then (436729252148359 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-358062848634593 /
    75000000000000000 : ℚ) else
  if p = (2, 1) then (-46157888797347 /
    25000000000000000 : ℚ) else
  if p = (2, 2) then (-17018814281257 /
    12500000000000000 : ℚ) else
  if p = (2, 3) then (242780724774913 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-17397962452283 /
    600000000000000000 : ℚ) else
  if p = (3, 1) then (22785605362703 /
    40000000000000000 : ℚ) else
  if p = (3, 2) then (9425859881739 /
    8000000000000000 : ℚ) else
  if p = (3, 3) then (-3842092751068021 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf617_polynomial_eq :
    lowerPullbackPolynomial 14 7 majorizationTriangle617 radialPowerData21.radius
      (certifiedRadialHeight radialPowerData21 radialPowerData32)
      (certifiedRadialSlope radialPowerData21) 0 =
        planeArrayPolynomial majorizationArray617 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 7 majorizationTriangle617
    cellMatrix_14_7 cellMatrix_14_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf617_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray617 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf617_kernel {p : ℝ × ℝ} (hp : majorizationTriangle617.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 7 majorizationTriangle617
    radialPowerData21 radialPowerData32 radialPowerData21_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray617
    majorizationLeaf617_polynomial_eq majorizationLeaf617_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 618. -/
def majorizationTriangle618 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 618. -/
def majorizationArray618 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (6092746780619066272365021663868106706103690883 /
    17826336565709475958547388825600000000000000000 : ℚ) else
  if p = (0, 1) then (29059894898545191942004968790675084534670718367 /
    316912650057057350374175801344000000000000000000 : ℚ) else
  if p = (0, 2) then (-3739176504832457 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (34353302576759 /
    90000000000000000 : ℚ) else
  if p = (1, 0) then (80675743488147955164370604122857222936322990301 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-2577061899111869 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (1801010150116711 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-81194964594591 /
    25000000000000000 : ℚ) else
  if p = (2, 0) then (-4808968955100629 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (2271952681420887 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (-2679112114112969 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (1556875288371641 /
    300000000000000000 : ℚ) else
  if p = (3, 0) then (18702898092799 /
    45000000000000000 : ℚ) else
  if p = (3, 1) then (-1043214844183313 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (783788314984399 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (-3842092751068021 /
    1800000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf618_polynomial_eq :
    lowerPullbackPolynomial 14 7 majorizationTriangle618 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray618 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 7 majorizationTriangle618
    cellMatrix_14_7 cellMatrix_14_7_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf618_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray618 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf618_kernel {p : ℝ × ℝ} (hp : majorizationTriangle618.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((7 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 7 majorizationTriangle618
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray618
    majorizationLeaf618_polynomial_eq majorizationLeaf618_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 619. -/
def majorizationTriangle619 : RationalTriangle := ⟨
  (0, 0),
  (1, 0),
  (0, 1)⟩

/-- Candidate rational monomial coefficients of leaf 619. -/
def majorizationArray619 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (1195191805929115796339885535670969195622242202743 /
    2852213850513516153367582212096000000000000000000 : ℚ) else
  if p = (0, 1) then (-82423210326116366337242045761387319245750231261 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (0, 2) then (-647665827376727 /
    120000000000000000 : ℚ) else
  if p = (0, 3) then (9117227461583 /
    200000000000000000 : ℚ) else
  if p = (1, 0) then (-66620949531784574331073664638789407834172907741 /
    950737950171172051122527404032000000000000000000 : ℚ) else
  if p = (1, 1) then (-119586224636721 /
    200000000000000000 : ℚ) else
  if p = (1, 2) then (422060818171631 /
    200000000000000000 : ℚ) else
  if p = (1, 3) then (-1609891575030197 /
    600000000000000000 : ℚ) else
  if p = (2, 0) then (-4060853031388669 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-185522993054261 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (456041145824627 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-1150684451649471 /
    200000000000000000 : ℚ) else
  if p = (3, 0) then (-18702898092799 /
    45000000000000000 : ℚ) else
  if p = (3, 1) then (-1043214844183313 /
    300000000000000000 : ℚ) else
  if p = (3, 2) then (-783788314984399 /
    150000000000000000 : ℚ) else
  if p = (3, 3) then (4706825946761123 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf619_polynomial_eq :
    lowerPullbackPolynomial 14 8 majorizationTriangle619 radialPowerData26.radius
      (certifiedRadialHeight radialPowerData26 radialPowerData32)
      (certifiedRadialSlope radialPowerData26) 0 =
        planeArrayPolynomial majorizationArray619 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 8 majorizationTriangle619
    cellMatrix_14_8 cellMatrix_14_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf619_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray619 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf619_kernel {p : ℝ × ℝ} (hp : majorizationTriangle619.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 8 majorizationTriangle619
    radialPowerData26 radialPowerData32 radialPowerData26_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray619
    majorizationLeaf619_polynomial_eq majorizationLeaf619_bernstein_nonneg hp
  simpa using h

/-- The actual closed rational triangle of majorization leaf 620. -/
def majorizationTriangle620 : RationalTriangle := ⟨
  (1, 1),
  (0, 1),
  (1, 0)⟩

/-- Candidate rational monomial coefficients of leaf 620. -/
def majorizationArray620 (p : ℕ × ℕ) : ℚ :=
  if p = (0, 0) then (17547162708909021681859144795116397849442643491 /
    71305346262837903834189555302400000000000000000 : ℚ) else
  if p = (0, 1) then (23856372059011826652088203967401846947786553443 /
    237684487542793012780631851008000000000000000000 : ℚ) else
  if p = (0, 2) then (-4722478407330671 /
    600000000000000000 : ℚ) else
  if p = (0, 3) then (54627883472123 /
    100000000000000000 : ℚ) else
  if p = (1, 0) then (7286807865015247534671244910720559131832363041 /
    79228162514264337593543950336000000000000000000 : ℚ) else
  if p = (1, 1) then (-114520528797789 /
    40000000000000000 : ℚ) else
  if p = (1, 2) then (-761093881047927 /
    40000000000000000 : ℚ) else
  if p = (1, 3) then (2803239777678173 /
    300000000000000000 : ℚ) else
  if p = (2, 0) then (-8993738856367241 /
    600000000000000000 : ℚ) else
  if p = (2, 1) then (-3038247575688131 /
    200000000000000000 : ℚ) else
  if p = (2, 2) then (7989312371221987 /
    200000000000000000 : ℚ) else
  if p = (2, 3) then (-889035373777913 /
    50000000000000000 : ℚ) else
  if p = (3, 0) then (2292386928341257 /
    1800000000000000000 : ℚ) else
  if p = (3, 1) then (1921247210680517 /
    200000000000000000 : ℚ) else
  if p = (3, 2) then (-10985324580345773 /
    600000000000000000 : ℚ) else
  if p = (3, 3) then (4706825946761123 /
    600000000000000000 : ℚ) else
  0

/-- The candidate is the actual signed lower polynomial, by ordinary kernel checks. -/
theorem majorizationLeaf620_polynomial_eq :
    lowerPullbackPolynomial 14 8 majorizationTriangle620 radialPowerData28.radius
      (certifiedRadialHeight radialPowerData28 radialPowerData32)
      (certifiedRadialSlope radialPowerData28) 0 =
        planeArrayPolynomial majorizationArray620 := by
  apply lowerPullbackPolynomial_eq_array_of_sparse_checks 14 8 majorizationTriangle620
    cellMatrix_14_8 cellMatrix_14_8_correct
  · decide +kernel
  · decide +kernel

/-- All twenty-eight actual Bernstein signs are ordinary kernel checks. -/
theorem majorizationLeaf620_bernstein_nonneg : ∀ p ∈ triangleIndices,
    0 ≤ triangleBernsteinCoefficient majorizationArray620 p.1 p.2 := by
  apply triangleBernstein_nonneg_of_fin_checks
  decide +kernel

/-- The actual kernel majorization holds on every point of the closed real triangle. -/
theorem majorizationLeaf620_kernel {p : ℝ × ℝ} (hp : majorizationTriangle620.Contains p) :
    (0 : ℝ) ≤ kernel (((14 : ℝ) + p.1) / 16) (((8 : ℝ) + p.2) / 16) := by
  have h := kernel_ge_target_on_checked_triangle 14 8 majorizationTriangle620
    radialPowerData28 radialPowerData32 radialPowerData28_valid radialPowerData32_valid
    (by norm_num [radialPowerData32, supportRadiusRat]) (0 : Fin 2)
    (by unfold RationalTriangle.InUnitBox vertexInUnitBox; decide +kernel)
    (by unfold RationalTriangle.HasRadiusBound; decide +kernel) majorizationArray620
    majorizationLeaf620_polynomial_eq majorizationLeaf620_bernstein_nonneg hp
  simpa using h

end PartialBalayage.Maximal.Square
