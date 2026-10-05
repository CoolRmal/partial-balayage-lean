/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonKatoWeak
public import PartialBalayage.Linear.ExtendedEnergyMassIdentity
public import PartialBalayage.Linear.DirichletDual

/-!
# Actual bounded Poisson Dirichlet operators

Zero extension, genuine normalized Poisson convolution, and domain restriction define a
self-adjoint contraction on the actual restricted real `L²` space. Its difference quotient
plus a positive scalar identity is a genuine positive coercive Dirichlet operator. These
bounded approximants permit actual measurable Kato directions as obstacle tests.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²" => Lp ℝ 2 (volume : Measure D)

/-- Actual normalized Poisson convolution is self-adjoint on real `L²`. -/
theorem real_inner_poissonConvolutionL2 {t : ℝ} (ht : 0 < t) (f g : L²) :
    ⟪f, poissonConvolutionL2 ht g⟫ = ⟪poissonConvolutionL2 ht f, g⟫ := by
  have h := congrArg Complex.re (inner_poissonConvolutionL2 ht
    (Complex.ofRealCLM.compLp f) (Complex.ofRealCLM.compLp g))
  rw [poissonConvolutionL2_compLp ht, poissonConvolutionL2_compLp ht,
    re_inner_complexifyL2, re_inner_complexifyL2] at h
  exact h

/-- The genuine restricted Poisson average of the zero extension. -/
def poissonDirichletAverage {Ω : Set D} (hΩ : MeasurableSet Ω) {t : ℝ} (ht : 0 < t) :
    Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  restrictL2CLM Ω ∘L poissonConvolutionL2CLM ht ∘L zeroExtendL2CLM hΩ

/-- Domain restriction and zero extension retain the actual `L²` contraction. -/
theorem norm_poissonDirichletAverage_le {Ω : Set D} (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 (volume.restrict Ω)) :
    ‖poissonDirichletAverage hΩ ht u‖ ≤ ‖u‖ := by
  exact (norm_restrictL2CLM_le Ω _).trans
    ((norm_poissonConvolutionL2_le ht _).trans (norm_zeroExtendL2 hΩ u).le)

/-- The actual finite-domain Poisson average remains self-adjoint. -/
theorem inner_poissonDirichletAverage {Ω : Set D} (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 < t) (u v : Lp ℝ 2 (volume.restrict Ω)) :
    ⟪u, poissonDirichletAverage hΩ ht v⟫ = ⟪poissonDirichletAverage hΩ ht u, v⟫ := by
  change ⟪u, restrictL2CLM Ω (poissonConvolutionL2 ht (zeroExtendL2 hΩ v))⟫ =
    ⟪restrictL2CLM Ω (poissonConvolutionL2 ht (zeroExtendL2 hΩ u)), v⟫
  rw [real_inner_comm _ u, ← inner_global_zeroExtendL2 hΩ, real_inner_comm,
    real_inner_poissonConvolutionL2 ht, inner_global_zeroExtendL2 hΩ]

/-- The actual regularized bounded Poisson difference quotient on the domain. -/
def poissonDirichletOperator {Ω : Set D} (hΩ : MeasurableSet Ω) {t : ℝ} (ht : 0 < t)
    (ε : ℝ) : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  ε • ContinuousLinearMap.id ℝ _ +
    t⁻¹ • (ContinuousLinearMap.id ℝ _ - poissonDirichletAverage hΩ ht)

/-- The actual operator's pairing separates its scalar regularization and Poisson defect. -/
theorem inner_poissonDirichletOperator {Ω : Set D} (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 < t) (ε : ℝ) (u v : Lp ℝ 2 (volume.restrict Ω)) :
    ⟪poissonDirichletOperator hΩ ht ε u, v⟫ =
      ε * ⟪u, v⟫ + t⁻¹ * (⟪u, v⟫ - ⟪poissonDirichletAverage hΩ ht u, v⟫) := by
  simp only [poissonDirichletOperator, add_apply,
    smul_apply, sub_apply,
    ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left, inner_sub_left]

/-- Positivity comes from the actual self-adjoint contraction, rather than a certificate. -/
theorem isPositive_poissonDirichletOperator {Ω : Set D} (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 < t) {ε : ℝ} (hε : 0 ≤ ε) :
    (poissonDirichletOperator hΩ ht ε).IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff _).mpr ⟨?_, ?_⟩
  · intro u v
    change ⟪poissonDirichletOperator hΩ ht ε u, v⟫ =
      ⟪u, poissonDirichletOperator hΩ ht ε v⟫
    rw [real_inner_comm _ u, inner_poissonDirichletOperator, inner_poissonDirichletOperator,
      real_inner_comm, ← inner_poissonDirichletAverage, real_inner_comm]
    rw [real_inner_comm u (poissonDirichletAverage hΩ ht v)]
  · intro u
    change 0 ≤ ⟪poissonDirichletOperator hΩ ht ε u, u⟫
    rw [inner_poissonDirichletOperator, real_inner_self_eq_norm_sq]
    have h := (real_inner_le_norm (poissonDirichletAverage hΩ ht u) u).trans
      (mul_le_mul_of_nonneg_right (norm_poissonDirichletAverage_le hΩ ht u) (norm_nonneg u))
    have hd : 0 ≤ ‖u‖ ^ 2 - ⟪poissonDirichletAverage hΩ ht u, u⟫ := by nlinarith
    exact add_nonneg (mul_nonneg hε (sq_nonneg _)) (mul_nonneg (inv_nonneg.mpr ht.le) hd)

/-- A positive scalar regularization makes the genuine bounded operator coercive. -/
theorem coercive_poissonDirichletOperator {Ω : Set D} (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 < t) {ε : ℝ} (_hε : 0 < ε) (u : Lp ℝ 2 (volume.restrict Ω)) :
    ε * ‖u‖ ^ 2 ≤ ⟪poissonDirichletOperator hΩ ht ε u, u⟫ := by
  rw [inner_poissonDirichletOperator, real_inner_self_eq_norm_sq]
  have h := (real_inner_le_norm (poissonDirichletAverage hΩ ht u) u).trans
    (mul_le_mul_of_nonneg_right (norm_poissonDirichletAverage_le hΩ ht u) (norm_nonneg u))
  have hd : 0 ≤ ‖u‖ ^ 2 - ⟪poissonDirichletAverage hΩ ht u, u⟫ := by nlinarith
  exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr ht.le) hd)

/-- The actual signed bounded-Poisson obstacle, with its genuine equation and alignment. -/
theorem exists_poissonDirichlet_signed_obstacle {Ω : Set D} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε)
    (f : Lp ℝ 2 (volume.restrict Ω)) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ (ν u : Lp ℝ 2 (volume.restrict Ω)), ν ∈ normCap (volume.restrict Ω) κ ∧
      poissonDirichletOperator hΩ ht ε u = f - ν ∧
      (∀ᵐ x ∂(volume.restrict Ω), u x ≠ 0 → ν x = (κ / ‖u x‖) • u x) ∧
      (∀ᵐ x ∂(volume.restrict Ω), u x ≠ 0 → ‖ν x‖ = κ) := by
  obtain ⟨ν, u, hν, _, heq, halign, hsat⟩ :=
    exists_dirichlet_dual_obstacle (volume.restrict Ω) (poissonDirichletOperator hΩ ht ε)
      (isPositive_poissonDirichletOperator hΩ ht hε.le) hε
      (coercive_poissonDirichletOperator hΩ ht hε) (ContinuousLinearMap.id ℝ _) f hκ
  simp only [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] at heq
  simpa only [ContinuousLinearMap.id_apply] using ⟨ν, u, hν, heq, halign, hsat⟩

end PartialBalayage.Linear
