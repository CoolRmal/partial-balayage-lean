/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.SobolevKernelSourceBound
public import PartialBalayage.Maximal.ScaledSemigroupSourceBound
public import PartialBalayage.Maximal.SemigroupMajorantMass

/-!
# Actual heat and Poisson Sobolev source comparisons

The genuine globally integrable tangent majorants satisfy the source inequality for actual
nonnegative L² distributional states. At zero contact, their forcing pairings are genuinely
integrable and nonnegative almost everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Ball
open PartialBalayage.Constants

namespace PartialBalayage

/-- The admissible actual heat majorant is nonnegative almost everywhere. -/
theorem heatKernelMajorant_nonneg_ae (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsHeatTangencyParameter n a) (ht : 0 < t) :
    ∀ᵐ y ∂volume, 0 ≤ heatKernelMajorant n a t y := by
  filter_upwards [heatKernel_le_majorant_ae n hn hroot ht] with y hy
  exact (heatKernel_pos n ht y).le.trans hy

/-- The admissible actual Poisson majorant is nonnegative almost everywhere. -/
theorem poissonKernelMajorant_nonneg_ae (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (ht : 0 < t) :
    ∀ᵐ y ∂volume, 0 ≤ poissonKernelMajorant n a t y := by
  filter_upwards [poissonKernel_le_majorant_ae n hn hroot ht] with y hy
  exact (poissonKernel_pos n ht y).le.trans hy

/-- The actual heat source comparison for a genuine nonnegative L² distributional state. -/
theorem heatKernelMajorant_source_bound_of_L2_distribution (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsHeatTangencyParameter n a) (ht : 0 < t)
    (u g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hu0 : ∀ᵐ y ∂volume, 0 ≤ u y) (hΔ : HasLocalDistributionalLaplacian n univ u g) :
    ∀ᵐ x ∂volume, -(heatKernelMajorantSourceMass n a t * u x) ≤
      ∫ y, heatKernelMajorant n a t (y - x) * g y := by
  have hρ := rho_pos n hn
  have ha : 0 < a := lt_of_le_of_lt (by positivity) hroot.1.1
  exact integrable_kernel_source_bound_of_L2_distribution (heatKernelMajorant n a t)
    (integrable_heatKernelMajorant n hn ha ht) (heatKernelMajorant_nonneg_ae n hn hroot ht)
    (heatKernelMajorantSourceMass n a t) (fun v hv hsupp hv0 ↦ by
      simpa only [sub_zero] using heatKernelMajorant_laplacian_source_bound n hn hroot ht
        v hv hsupp hv0 0) u g hu0 hΔ

/-- The actual Poisson source comparison for a genuine nonnegative L² distributional state. -/
theorem poissonKernelMajorant_source_bound_of_L2_distribution (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (ht : 0 < t)
    (u g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hu0 : ∀ᵐ y ∂volume, 0 ≤ u y) (hΔ : HasLocalDistributionalLaplacian n univ u g) :
    ∀ᵐ x ∂volume, -(poissonKernelMajorantSourceMass n a t * u x) ≤
      ∫ y, poissonKernelMajorant n a t (y - x) * g y := by
  have hρ := rho_pos n hn
  have ha : 0 < a := lt_of_le_of_lt (by positivity) hroot.1.1
  exact integrable_kernel_source_bound_of_L2_distribution (poissonKernelMajorant n a t)
    (integrable_poissonKernelMajorant n hn ha ht)
    (poissonKernelMajorant_nonneg_ae n hn hroot ht) (poissonKernelMajorantSourceMass n a t)
    (fun v hv hsupp hv0 ↦ by
      simpa only [sub_zero] using poissonKernelMajorant_laplacian_source_bound n hn hroot ht
        v hv hsupp hv0 0) u g hu0 hΔ

/-- Actual heat forcing pairings are integrable and nonnegative on zero contact a.e. -/
theorem heatKernelMajorant_pairing_nonneg_on_L2_contact (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsHeatTangencyParameter n a) (ht : 0 < t)
    (u g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hu0 : ∀ᵐ y ∂volume, 0 ≤ u y) (hΔ : HasLocalDistributionalLaplacian n univ u g) :
    ∀ᵐ x ∂volume, Integrable (fun y ↦ heatKernelMajorant n a t (y - x) * g y) ∧
      (u x = 0 → 0 ≤ ∫ y, heatKernelMajorant n a t (y - x) * g y) := by
  have hρ := rho_pos n hn
  have ha : 0 < a := lt_of_le_of_lt (by positivity) hroot.1.1
  exact integrable_kernel_pairing_nonneg_on_L2_contact (heatKernelMajorant n a t)
    (integrable_heatKernelMajorant n hn ha ht) (heatKernelMajorant_nonneg_ae n hn hroot ht)
    (heatKernelMajorantSourceMass n a t) (fun v hv hsupp hv0 ↦ by
      simpa only [sub_zero] using heatKernelMajorant_laplacian_source_bound n hn hroot ht
        v hv hsupp hv0 0) u g hu0 hΔ

/-- Actual Poisson forcing pairings are integrable and nonnegative on zero contact a.e. -/
theorem poissonKernelMajorant_pairing_nonneg_on_L2_contact (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (ht : 0 < t)
    (u g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hu0 : ∀ᵐ y ∂volume, 0 ≤ u y) (hΔ : HasLocalDistributionalLaplacian n univ u g) :
    ∀ᵐ x ∂volume, Integrable (fun y ↦ poissonKernelMajorant n a t (y - x) * g y) ∧
      (u x = 0 → 0 ≤ ∫ y, poissonKernelMajorant n a t (y - x) * g y) := by
  have hρ := rho_pos n hn
  have ha : 0 < a := lt_of_le_of_lt (by positivity) hroot.1.1
  exact integrable_kernel_pairing_nonneg_on_L2_contact (poissonKernelMajorant n a t)
    (integrable_poissonKernelMajorant n hn ha ht)
    (poissonKernelMajorant_nonneg_ae n hn hroot ht) (poissonKernelMajorantSourceMass n a t)
    (fun v hv hsupp hv0 ↦ by
      simpa only [sub_zero] using poissonKernelMajorant_laplacian_source_bound n hn hroot ht
        v hv hsupp hv0 0) u g hu0 hΔ

end PartialBalayage
