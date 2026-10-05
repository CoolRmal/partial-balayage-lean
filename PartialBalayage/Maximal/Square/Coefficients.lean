/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

/-!
# Frozen rational coefficients of the order-6/5 square kernel

These are the 169 literal orbit entries from the supplementary coefficient file with SHA256
`982e6f8aaccbd06571e65582d0fdfa8537b24ea31501dbd2f7db3e730dd32f2f`.
The mathematical checks below are Lean proofs. The external result files are not hypotheses.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 4096

/-- Literal coefficient orbit block 1 of 13. -/
def splineOrbits0 : List (ℕ × ℕ × ℚ) := [
  (0, 0, (-2568121280114976561 : ℚ) / 50000000000000000),
  (1, 0, (-3580726744280741 : ℚ) / 25000000000000000),
  (1, 1, (-856126613391259033 : ℚ) / 50000000000000000),
  (2, 0, (-18588823155675923 : ℚ) / 6250000000000000),
  (2, 1, (-47742345216275913 : ℚ) / 10000000000000000),
  (2, 2, (-401384398698637221 : ℚ) / 50000000000000000),
  (3, 0, (-84109406663386373 : ℚ) / 50000000000000000),
  (3, 1, (-133829754398586131 : ℚ) / 50000000000000000),
  (3, 2, (-155686969147710751 : ℚ) / 50000000000000000),
  (3, 3, (-113445003217355137 : ℚ) / 25000000000000000),
  (4, 0, (-13856844979173323 : ℚ) / 12500000000000000),
  (4, 1, (-74002558040022417 : ℚ) / 50000000000000000),
  (4, 2, (-85954352582810701 : ℚ) / 50000000000000000)
]

/-- Literal coefficient orbit block 2 of 13. -/
def splineOrbits1 : List (ℕ × ℕ × ℚ) := [
  (4, 3, (-46178784630491377 : ℚ) / 25000000000000000),
  (4, 4, (-3297746187654601 : ℚ) / 1562500000000000),
  (5, 0, (-3394332195509623 : ℚ) / 5000000000000000),
  (5, 1, (-21325766694303087 : ℚ) / 25000000000000000),
  (5, 2, (-23668750061252291 : ℚ) / 25000000000000000),
  (5, 3, (-11750949550027257 : ℚ) / 12500000000000000),
  (5, 4, (-9959285551542257 : ℚ) / 12500000000000000),
  (5, 5, (-22892794888393781 : ℚ) / 50000000000000000),
  (6, 0, (-10065076963985693 : ℚ) / 25000000000000000),
  (6, 1, (-12346066895131189 : ℚ) / 25000000000000000),
  (6, 2, (-26487651107730747 : ℚ) / 50000000000000000),
  (6, 3, (-992735617425379 : ℚ) / 2000000000000000),
  (6, 4, (-19018576753198569 : ℚ) / 50000000000000000)
]

/-- Literal coefficient orbit block 3 of 13. -/
def splineOrbits2 : List (ℕ × ℕ × ℚ) := [
  (6, 5, (-9955381214687611 : ℚ) / 50000000000000000),
  (6, 6, (-2991433750673721 : ℚ) / 50000000000000000),
  (7, 0, (-5634479244055247 : ℚ) / 25000000000000000),
  (7, 1, (-6869398073810269 : ℚ) / 25000000000000000),
  (7, 2, (-2864631798466393 : ℚ) / 10000000000000000),
  (7, 3, (-12594631333769657 : ℚ) / 50000000000000000),
  (7, 4, (-526585871531821 : ℚ) / 3125000000000000),
  (7, 5, (-2880673058832033 : ℚ) / 50000000000000000),
  (7, 6, (279468807356327 : ℚ) / 10000000000000000),
  (7, 7, (102122522341111 : ℚ) / 1250000000000000),
  (8, 0, (-5423961281863997 : ℚ) / 50000000000000000),
  (8, 1, (-3409564126690437 : ℚ) / 25000000000000000),
  (8, 2, (-3423106913693723 : ℚ) / 25000000000000000)
]

/-- Literal coefficient orbit block 4 of 13. -/
def splineOrbits3 : List (ℕ × ℕ × ℚ) := [
  (8, 3, (-133011156015623 : ℚ) / 1250000000000000),
  (8, 4, (-1154488170063279 : ℚ) / 25000000000000000),
  (8, 5, (165517439978989 : ℚ) / 6250000000000000),
  (8, 6, (4049833640299743 : ℚ) / 50000000000000000),
  (8, 7, (2830256951905451 : ℚ) / 25000000000000000),
  (8, 8, (782052399850243 : ℚ) / 6250000000000000),
  (9, 0, (-76860257087183 : ℚ) / 2500000000000000),
  (9, 1, (-2343811924526677 : ℚ) / 50000000000000000),
  (9, 2, (-1059092386238759 : ℚ) / 25000000000000000),
  (9, 3, (-168038290738859 : ℚ) / 10000000000000000),
  (9, 4, (685088082228027 : ℚ) / 25000000000000000),
  (9, 5, (1910504912058067 : ℚ) / 25000000000000000),
  (9, 6, (1378755705574379 : ℚ) / 12500000000000000)
]

/-- Literal coefficient orbit block 5 of 13. -/
def splineOrbits4 : List (ℕ × ℕ × ℚ) := [
  (9, 7, (3139443317450451 : ℚ) / 25000000000000000),
  (9, 8, (383128398398939 : ℚ) / 3125000000000000),
  (9, 9, (1210229758244737 : ℚ) / 12500000000000000),
  (10, 0, (524708884971933 : ℚ) / 25000000000000000),
  (10, 1, (590408454972003 : ℚ) / 50000000000000000),
  (10, 2, (910723543458021 : ℚ) / 50000000000000000),
  (10, 3, (1965153920312457 : ℚ) / 50000000000000000),
  (10, 4, (1790625021507691 : ℚ) / 25000000000000000),
  (10, 5, (326813801122301 : ℚ) / 3125000000000000),
  (10, 6, (61866133164717 : ℚ) / 500000000000000),
  (10, 7, (1562768339077787 : ℚ) / 12500000000000000),
  (10, 8, (1322355531220889 : ℚ) / 12500000000000000),
  (10, 9, (609257499828017 : ℚ) / 12500000000000000)
]

/-- Literal coefficient orbit block 6 of 13. -/
def splineOrbits5 : List (ℕ × ℕ × ℚ) := [
  (10, 10, (-3844547517640133 : ℚ) / 25000000000000000),
  (11, 0, (285007293089521 : ℚ) / 5000000000000000),
  (11, 1, (40376166142893 : ℚ) / 781250000000000),
  (11, 2, (588302015249093 : ℚ) / 10000000000000000),
  (11, 3, (950329600747729 : ℚ) / 12500000000000000),
  (11, 4, (200495957260967 : ℚ) / 2000000000000000),
  (11, 5, (3063464886527067 : ℚ) / 25000000000000000),
  (11, 6, (6606464960508007 : ℚ) / 50000000000000000),
  (11, 7, (1574232952544499 : ℚ) / 12500000000000000),
  (11, 8, (1596924746507 : ℚ) / 16000000000000),
  (11, 9, (2112488422289457 : ℚ) / 50000000000000000),
  (11, 10, (-4508866076253473 : ℚ) / 50000000000000000),
  (11, 11, (-6741463368158923 : ℚ) / 12500000000000000)
]

/-- Literal coefficient orbit block 7 of 13. -/
def splineOrbits6 : List (ℕ × ℕ × ℚ) := [
  (12, 0, (2097310318630857 : ℚ) / 25000000000000000),
  (12, 1, (4061648656663241 : ℚ) / 50000000000000000),
  (12, 2, (138160083396877 : ℚ) / 1562500000000000),
  (12, 3, (257496318967191 : ℚ) / 2500000000000000),
  (12, 4, (6082180233017581 : ℚ) / 50000000000000000),
  (12, 5, (3438831546859809 : ℚ) / 25000000000000000),
  (12, 6, (7129109610407073 : ℚ) / 50000000000000000),
  (12, 7, (6721385442867153 : ℚ) / 50000000000000000),
  (12, 8, (5586655192328267 : ℚ) / 50000000000000000),
  (12, 9, (686414287375281 : ℚ) / 10000000000000000),
  (12, 10, (-139955844595041 : ℚ) / 25000000000000000),
  (12, 11, (-149370870103451 : ℚ) / 1562500000000000),
  (12, 12, (-13726372155635567 : ℚ) / 50000000000000000)
]

/-- Literal coefficient orbit block 8 of 13. -/
def splineOrbits7 : List (ℕ × ℕ × ℚ) := [
  (13, 0, (2571362998778819 : ℚ) / 25000000000000000),
  (13, 1, (254277596827161 : ℚ) / 2500000000000000),
  (13, 2, (5433385769358511 : ℚ) / 50000000000000000),
  (13, 3, (6046736681076787 : ℚ) / 50000000000000000),
  (13, 4, (423649743148241 : ℚ) / 3125000000000000),
  (13, 5, (229645002794059 : ℚ) / 1562500000000000),
  (13, 6, (1861487512248211 : ℚ) / 12500000000000000),
  (13, 7, (3506716236790023 : ℚ) / 25000000000000000),
  (13, 8, (6014458512822711 : ℚ) / 50000000000000000),
  (13, 9, (4416746335440497 : ℚ) / 50000000000000000),
  (13, 10, (944116559245703 : ℚ) / 25000000000000000),
  (13, 11, (-529492956971297 : ℚ) / 25000000000000000),
  (14, 0, (5717547766736913 : ℚ) / 50000000000000000)
]

/-- Literal coefficient orbit block 9 of 13. -/
def splineOrbits8 : List (ℕ × ℕ × ℚ) := [
  (14, 1, (5706353438696041 : ℚ) / 50000000000000000),
  (14, 2, (3011657059182359 : ℚ) / 25000000000000000),
  (14, 3, (1631917691321587 : ℚ) / 12500000000000000),
  (14, 4, (708161724221513 : ℚ) / 5000000000000000),
  (14, 5, (3726634163163701 : ℚ) / 25000000000000000),
  (14, 6, (7399777168736501 : ℚ) / 50000000000000000),
  (14, 7, (1372684514015929 : ℚ) / 10000000000000000),
  (14, 8, (736178485417493 : ℚ) / 6250000000000000),
  (14, 9, (2149852408074433 : ℚ) / 25000000000000000),
  (14, 10, (2683271435523521 : ℚ) / 50000000000000000),
  (15, 0, (2995283711051263 : ℚ) / 25000000000000000),
  (15, 1, (37501169611987 : ℚ) / 312500000000000),
  (15, 2, (627270426500573 : ℚ) / 5000000000000000)
]

/-- Literal coefficient orbit block 10 of 13. -/
def splineOrbits9 : List (ℕ × ℕ × ℚ) := [
  (15, 3, (6664609434033973 : ℚ) / 50000000000000000),
  (15, 4, (7046707019911967 : ℚ) / 50000000000000000),
  (15, 5, (902667740238249 : ℚ) / 6250000000000000),
  (15, 6, (3485025851328359 : ℚ) / 25000000000000000),
  (15, 7, (785172379977059 : ℚ) / 6250000000000000),
  (15, 8, (5011581557654961 : ℚ) / 50000000000000000),
  (15, 9, (1782553338520101 : ℚ) / 25000000000000000),
  (16, 0, (6029979513667601 : ℚ) / 50000000000000000),
  (16, 1, (6033908044461399 : ℚ) / 50000000000000000),
  (16, 2, (6255333500772997 : ℚ) / 50000000000000000),
  (16, 3, (6525643050685163 : ℚ) / 50000000000000000),
  (16, 4, (3366416501899391 : ℚ) / 25000000000000000),
  (16, 5, (1671415764193933 : ℚ) / 12500000000000000)
]

/-- Literal coefficient orbit block 11 of 13. -/
def splineOrbits10 : List (ℕ × ℕ × ℚ) := [
  (16, 6, (1553207281587639 : ℚ) / 12500000000000000),
  (16, 7, (642597456630331 : ℚ) / 6250000000000000),
  (16, 8, (472344886475671 : ℚ) / 6250000000000000),
  (17, 0, (732669875171551 : ℚ) / 6250000000000000),
  (17, 1, (5875915034340159 : ℚ) / 50000000000000000),
  (17, 2, (6021895414318499 : ℚ) / 50000000000000000),
  (17, 3, (3081212747835737 : ℚ) / 25000000000000000),
  (17, 4, (3083923816455491 : ℚ) / 25000000000000000),
  (17, 5, (5877721335472211 : ℚ) / 50000000000000000),
  (17, 6, (4995863851301487 : ℚ) / 50000000000000000),
  (17, 7, (752865296771777 : ℚ) / 10000000000000000),
  (18, 0, (346960814882227 : ℚ) / 3125000000000000),
  (18, 1, (1109132129692757 : ℚ) / 10000000000000000)
]

/-- Literal coefficient orbit block 12 of 13. -/
def splineOrbits11 : List (ℕ × ℕ × ℚ) := [
  (18, 2, (2806231282398733 : ℚ) / 25000000000000000),
  (18, 3, (1398261849433723 : ℚ) / 12500000000000000),
  (18, 4, (1344874469269527 : ℚ) / 12500000000000000),
  (18, 5, (935683923446441 : ℚ) / 10000000000000000),
  (18, 6, (3632883487353533 : ℚ) / 50000000000000000),
  (19, 0, (2554134159347147 : ℚ) / 25000000000000000),
  (19, 1, (254101352364477 : ℚ) / 2500000000000000),
  (19, 2, (5038952997425251 : ℚ) / 50000000000000000),
  (19, 3, (4845162249668189 : ℚ) / 50000000000000000),
  (19, 4, (4267294155136839 : ℚ) / 50000000000000000),
  (19, 5, (1688946349157141 : ℚ) / 25000000000000000),
  (20, 0, (35700467819813 : ℚ) / 390625000000000),
  (20, 1, (224363038690463 : ℚ) / 2500000000000000)
]

/-- Literal coefficient orbit block 13 of 13. -/
def splineOrbits12 : List (ℕ × ℕ × ℚ) := [
  (20, 2, (4330886187504219 : ℚ) / 50000000000000000),
  (20, 3, (3807460454644667 : ℚ) / 50000000000000000),
  (20, 4, (305021240184111 : ℚ) / 5000000000000000),
  (21, 0, (155762062438779 : ℚ) / 2000000000000000),
  (21, 1, (3808514547843447 : ℚ) / 50000000000000000),
  (21, 2, (3366968690632743 : ℚ) / 50000000000000000),
  (21, 3, (684347342461457 : ℚ) / 12500000000000000),
  (22, 0, (1618083319442729 : ℚ) / 25000000000000000),
  (22, 1, (2892234877238267 : ℚ) / 50000000000000000),
  (22, 2, (2453520659103157 : ℚ) / 50000000000000000),
  (23, 0, (1092892916193783 : ℚ) / 25000000000000000),
  (23, 1, (54721535176357 : ℚ) / 1250000000000000),
  (24, 0, (1943625556391327 : ℚ) / 50000000000000000)
]

/-- The frozen coefficient orbits, indexed by nonnegative ordered integer pairs. -/
def splineOrbits : List (ℕ × ℕ × ℚ) :=
  splineOrbits0 ++ splineOrbits1 ++ splineOrbits2 ++ splineOrbits3 ++
    splineOrbits4 ++ splineOrbits5 ++ splineOrbits6 ++ splineOrbits7 ++
    splineOrbits8 ++ splineOrbits9 ++ splineOrbits10 ++ splineOrbits11 ++
    splineOrbits12

/-- All sign changes and coordinate interchanges of one nonnegative index pair. -/
def splineOrbit (i j : ℕ) : Finset (ℤ × ℤ) :=
  {((i : ℤ), (j : ℤ)), ((i : ℤ), -(j : ℤ)), (-(i : ℤ), (j : ℤ)),
    (-(i : ℤ), -(j : ℤ)), ((j : ℤ), (i : ℤ)), ((j : ℤ), -(i : ℤ)),
    (-(j : ℤ), (i : ℤ)), (-(j : ℤ), -(i : ℤ))}

/-- The exact signed tensor coefficient at an arbitrary integer index. -/
def splineCoefficient (i j : ℤ) : ℚ :=
  (splineOrbits.map (fun t ↦ if (i, j) ∈ splineOrbit t.1 t.2.1 then t.2.2 else 0)).sum

/-- The genuine orbit cardinality is used in the exact coefficient count and sum. -/
def orbitCardinalSum : ℕ :=
  (splineOrbits.map (fun t ↦ (splineOrbit t.1 t.2.1).card)).sum

/-- The exact signed sum of all tensor coefficients, with true orbit multiplicities. -/
def coefficientSum : ℚ :=
  (splineOrbits.map (fun t ↦ ((splineOrbit t.1 t.2.1).card : ℚ) * t.2.2)).sum

/-- The immutable candidate contains exactly 169 orbit entries. -/
theorem splineOrbits_length : splineOrbits.length = 169 := by decide

/-- Every orbit representative is ordered and every entire support fits the radius-7/4 diamond. -/
theorem splineOrbits_admissible :
    ∀ t ∈ splineOrbits, t.2.1 ≤ t.1 ∧ t.1 + t.2.1 + 4 ≤ 28 := by decide

/-- The literal representative index pairs are distinct. -/
theorem splineOrbits_indices_nodup : (splineOrbits.map (fun t ↦ (t.1, t.2.1))).Nodup := by
  decide

/-- Exact finite arithmetic gives the advertised 1,201 tensor entries. -/
theorem orbitCardinalSum_eq : orbitCardinalSum = 1201 := by decide

set_option maxHeartbeats 2000000 in
/-- Exact rational arithmetic recovers the signed coefficient sum in the mass formula. -/
theorem coefficientSum_eq :
    coefficientSum = -(3114374068343977777 / 10000000000000000 : ℚ) := by
  norm_num (config := { maxSteps := 1000000 }) [coefficientSum, splineOrbits, splineOrbit,
    splineOrbits0, splineOrbits1, splineOrbits2, splineOrbits3, splineOrbits4, splineOrbits5,
    splineOrbits6, splineOrbits7, splineOrbits8, splineOrbits9, splineOrbits10,
    splineOrbits11, splineOrbits12]

/-- The actual index orbit is invariant under interchange. -/
theorem mem_splineOrbit_swap (i j : ℕ) (a b : ℤ) :
    (a, b) ∈ splineOrbit i j ↔ (b, a) ∈ splineOrbit i j := by
  simp only [splineOrbit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  tauto

/-- The actual index orbit is invariant under negating the first coordinate. -/
theorem mem_splineOrbit_neg_left (i j : ℕ) (a b : ℤ) :
    (a, b) ∈ splineOrbit i j ↔ (-a, b) ∈ splineOrbit i j := by
  simp only [splineOrbit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  simp only [neg_eq_iff_eq_neg, neg_neg]
  tauto

/-- The actual index orbit is invariant under negating the second coordinate. -/
theorem mem_splineOrbit_neg_right (i j : ℕ) (a b : ℤ) :
    (a, b) ∈ splineOrbit i j ↔ (a, -b) ∈ splineOrbit i j := by
  exact (mem_splineOrbit_swap i j a b).trans
    ((mem_splineOrbit_neg_left i j b a).trans (mem_splineOrbit_swap i j (-b) a))

/-- Every actual orbit index has the representative absolute values, in either order. -/
theorem natAbs_of_mem_splineOrbit {i j : ℕ} {a b : ℤ} (h : (a, b) ∈ splineOrbit i j) :
    (a.natAbs = i ∧ b.natAbs = j) ∨ (a.natAbs = j ∧ b.natAbs = i) := by
  simp only [splineOrbit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with h | h | h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;> simp

/-- Two ordered nonnegative orbit representatives sharing an index are identical. -/
theorem splineOrbit_representative_unique {i j k l : ℕ} (hji : j ≤ i) (hlk : l ≤ k)
    {a b : ℤ} (hij : (a, b) ∈ splineOrbit i j) (hkl : (a, b) ∈ splineOrbit k l) :
    i = k ∧ j = l := by
  have h₁ := natAbs_of_mem_splineOrbit hij
  have h₂ := natAbs_of_mem_splineOrbit hkl
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> omega

/-- The exact coefficient function is invariant under coordinate interchange. -/
theorem splineCoefficient_swap (a b : ℤ) : splineCoefficient a b = splineCoefficient b a := by
  simp only [splineCoefficient, mem_splineOrbit_swap]

/-- The exact coefficient function is even in its first coordinate. -/
theorem splineCoefficient_neg_left (a b : ℤ) :
    splineCoefficient (-a) b = splineCoefficient a b := by
  simp only [splineCoefficient, ← mem_splineOrbit_neg_left]

/-- The exact coefficient function is even in its second coordinate. -/
theorem splineCoefficient_neg_right (a b : ℤ) :
    splineCoefficient a (-b) = splineCoefficient a b := by
  simp only [splineCoefficient, ← mem_splineOrbit_neg_right]

end PartialBalayage.Maximal.Square
