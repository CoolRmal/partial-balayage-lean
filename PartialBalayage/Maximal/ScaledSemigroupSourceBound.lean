/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.SemigroupKernelSourceBound

/-!
# Point-source bounds for the normalized time kernels

The complete harmonic source bound survives affine dilation and the actual positive heat and
Poisson normalization factors. This form permits positive smooth approximations whose center
values converge to zero without vanishing identically there.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open PartialBalayage.Constants

namespace PartialBalayage

/-- The negative point-source mass of the normalized heat harmonic-majorant kernel. -/
def heatKernelMajorantSourceMass (n : ℕ) (a t : ℝ) : ℝ :=
  heatMajorantNormalization n t *
    (Real.sqrt (4 * t) ^ n / Real.sqrt (4 * t) ^ 2) *
      (2 * heatInnerInwardFlux n a * radialSphereArea n)

/-- The negative point-source mass of the normalized Poisson harmonic-majorant kernel. -/
def poissonKernelMajorantSourceMass (n : ℕ) (a t : ℝ) : ℝ :=
  poissonMajorantNormalization n t * (t ^ n / t ^ 2) *
    (2 * poissonInnerInwardFlux n a * radialSphereArea n)

/-- The complete source bound scales with the volume factor divided by the Laplacian factor. -/
theorem scaled_radial_laplacian_source_bound (n : ℕ) (φ : ℝ → ℝ) (C : ℝ)
    (hφ : ∀ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 v →
      HasCompactSupport v → (∀ z, 0 ≤ v z) →
        -(C * v 0) ≤ ∫ z, φ ‖z‖ * Laplacian.laplacian v z)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (hwpos : ∀ y, 0 ≤ w y)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    -(r ^ n / r ^ 2 * C * w x) ≤
      ∫ y, φ (‖y - x‖ / r) * Laplacian.laplacian w y := by
  have hv := contDiff_comp_add_smul n w hw x r
  have hvsupp := hasCompactSupport_comp_add_smul n w hsupp x hr
  have hbase := hφ _ hv hvsupp (fun z ↦ hwpos _)
  have h := mul_le_mul_of_nonneg_left hbase (pow_nonneg hr.le n)
  rw [← integral_scaled_radial_mul_laplacian n w hw x φ hr] at h
  simp only [smul_zero, add_zero] at h
  calc
    _ = (r ^ n * -(C * w x)) / r ^ 2 := by ring
    _ ≤ _ := (div_le_iff₀ (pow_pos hr 2)).mpr (by simpa only [mul_comm] using h)

theorem heatKernelMajorantSourceMass_nonneg (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsHeatTangencyParameter n a) (ht : 0 < t) :
    0 ≤ heatKernelMajorantSourceMass n a t := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := rho_pos n hn
  have ha : 0 < a := lt_trans (by positivity) hroot.1.1
  have hfactor := heatMajorantNormalization_pos n ht
  have harea : 0 ≤ radialSphereArea n := by
    simp only [radialSphereArea, Measure.real]
    positivity
  unfold heatKernelMajorantSourceMass heatInnerInwardFlux
  positivity

theorem poissonKernelMajorantSourceMass_nonneg (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (ht : 0 < t) :
    0 ≤ poissonKernelMajorantSourceMass n a t := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := rho_pos n hn
  have ha : 0 < a := lt_trans (by positivity) hroot.1.1
  have hfactor := poissonMajorantNormalization_pos n ht
  have harea : 0 ≤ radialSphereArea n := by
    simp only [radialSphereArea, Measure.real]
    positivity
  unfold poissonKernelMajorantSourceMass poissonInnerInwardFlux
  positivity

/-- The actual normalized heat majorant has the complete point-source bound at every time. -/
theorem heatKernelMajorant_laplacian_source_bound (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsHeatTangencyParameter n a) (ht : 0 < t)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (hwpos : ∀ y, 0 ≤ w y)
    (x : EuclideanSpace ℝ (Fin n)) :
    -(heatKernelMajorantSourceMass n a t * w x) ≤
      ∫ y, heatKernelMajorant n a t (y - x) * Laplacian.laplacian w y := by
  have hi := scaled_radial_laplacian_source_bound n
    (fun r ↦ heatMajorantProfile n a (r ^ 2))
    (2 * heatInnerInwardFlux n a * radialSphereArea n) (fun v hv hvsupp hvpos ↦ by
      simpa only [sub_zero] using heatMajorantProfile_laplacian_source_bound n hn hroot
        v hv hvsupp hvpos 0) w hw hsupp hwpos x
        (Real.sqrt_pos.mpr (by positivity : 0 < 4 * t))
  have heq : (fun y ↦ heatKernelMajorant n a t (y - x) * Laplacian.laplacian w y) =
      (fun y ↦ heatMajorantNormalization n t *
        (heatMajorantProfile n a ((‖y - x‖ / Real.sqrt (4 * t)) ^ 2) *
          Laplacian.laplacian w y)) := by
    funext y
    unfold heatKernelMajorant
    ring
  rw [heq, integral_const_mul]
  have h := mul_le_mul_of_nonneg_left hi (heatMajorantNormalization_pos n ht).le
  convert h using 1
  unfold heatKernelMajorantSourceMass
  ring

/-- The actual normalized Poisson majorant has the complete point-source bound at every height. -/
theorem poissonKernelMajorant_laplacian_source_bound (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (ht : 0 < t)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (hwpos : ∀ y, 0 ≤ w y)
    (x : EuclideanSpace ℝ (Fin n)) :
    -(poissonKernelMajorantSourceMass n a t * w x) ≤
      ∫ y, poissonKernelMajorant n a t (y - x) * Laplacian.laplacian w y := by
  have hi := scaled_radial_laplacian_source_bound n
    (fun r ↦ poissonMajorantProfile n a (r ^ 2))
    (2 * poissonInnerInwardFlux n a * radialSphereArea n) (fun v hv hvsupp hvpos ↦ by
      simpa only [sub_zero] using poissonMajorantProfile_laplacian_source_bound n hn hroot
        v hv hvsupp hvpos 0) w hw hsupp hwpos x ht
  have heq : (fun y ↦ poissonKernelMajorant n a t (y - x) * Laplacian.laplacian w y) =
      (fun y ↦ poissonMajorantNormalization n t *
        (poissonMajorantProfile n a ((‖y - x‖ / t) ^ 2) * Laplacian.laplacian w y)) := by
    funext y
    unfold poissonKernelMajorant
    ring
  rw [heq, integral_const_mul]
  have h := mul_le_mul_of_nonneg_left hi (poissonMajorantNormalization_pos n ht).le
  convert h using 1
  unfold poissonKernelMajorantSourceMass
  ring

end PartialBalayage
