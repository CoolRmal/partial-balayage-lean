/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.AffineRadialScaling
public import PartialBalayage.Maximal.SemigroupDefinitions

/-!
# Normalized heat and Poisson harmonic majorants at positive times

The article's harmonic radial majorants are dilated and multiplied by the exact normalization
factors of the ordinary heat and Poisson kernels. Domination is stated off the origin and almost
everywhere, since real logarithms and powers assign artificial values to the singular center.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Constants

namespace PartialBalayage

/-- The exact positive normalization factor of a heat profile at time `t`. -/
def heatMajorantNormalization (n : ℕ) (t : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(n : ℝ) / 2)

/-- The exact positive normalization factor of a Poisson profile at height `t`. -/
def poissonMajorantNormalization (n : ℕ) (t : ℝ) : ℝ :=
  Real.Gamma (((n : ℝ) + 1) / 2) / Real.pi ^ (((n : ℝ) + 1) / 2) * t ^ (-(n : ℝ))

/-- The actual heat harmonic-majorant kernel at time `t`, in the same units as `heatKernel`. -/
def heatKernelMajorant (n : ℕ) (a t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  heatMajorantNormalization n t *
    heatMajorantProfile n a ((‖x‖ / Real.sqrt (4 * t)) ^ 2)

/-- The actual Poisson harmonic-majorant kernel at height `t`, normalized as `poissonKernel`. -/
def poissonKernelMajorant (n : ℕ) (a t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  poissonMajorantNormalization n t * poissonMajorantProfile n a ((‖x‖ / t) ^ 2)

theorem heatMajorantNormalization_pos (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < heatMajorantNormalization n t := by
  unfold heatMajorantNormalization
  positivity

theorem poissonMajorantNormalization_pos (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < poissonMajorantNormalization n t := by
  have hΓ := Real.Gamma_pos_of_pos (by positivity : 0 < ((n : ℝ) + 1) / 2)
  unfold poissonMajorantNormalization
  positivity

/-- The heat kernel is precisely its normalized ordinary-radius profile. -/
theorem heatKernel_eq_scaled_profile (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    heatKernel n t x = heatMajorantNormalization n t *
      Real.exp (-((‖x‖ / Real.sqrt (4 * t)) ^ 2)) := by
  simp only [heatKernel, heatMajorantNormalization, div_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 4 * t), neg_div]

/-- The Poisson kernel is precisely its normalized ordinary-radius profile. -/
theorem poissonKernel_eq_scaled_profile (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    poissonKernel n t x = poissonMajorantNormalization n t *
      (1 + (‖x‖ / t) ^ 2) ^ (-(((n : ℝ) + 1) / 2)) := by
  have hbase : 0 < 1 + (‖x‖ / t) ^ 2 := by positivity
  have hfactor : t ^ 2 + ‖x‖ ^ 2 = t ^ 2 * (1 + (‖x‖ / t) ^ 2) := by
    field_simp
  have hpower : (t ^ 2) ^ (((n : ℝ) + 1) / 2) = t ^ ((n : ℝ) + 1) := by
    rw [← Real.rpow_two t, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hcancel : t ^ (-(n : ℝ)) * t ^ ((n : ℝ) + 1) = t := by
    rw [← Real.rpow_add ht, show -(n : ℝ) + ((n : ℝ) + 1) = 1 by ring, Real.rpow_one]
  have hquot : t / t ^ ((n : ℝ) + 1) = t ^ (-(n : ℝ)) :=
    (div_eq_iff (Real.rpow_pos_of_pos ht _).ne').mpr hcancel.symm
  unfold poissonKernel poissonMajorantNormalization
  rw [hfactor, Real.mul_rpow (sq_nonneg t) hbase.le, hpower, div_mul_eq_div_div,
    mul_div_assoc, hquot, div_eq_mul_inv, ← Real.rpow_neg hbase.le]

/-- The scaled heat harmonic tangent dominates the actual heat kernel off its singular center. -/
theorem heatKernel_le_majorant (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsHeatTangencyParameter n a) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    heatKernel n t x ≤ heatKernelMajorant n a t x := by
  have hs : 0 < Real.sqrt (4 * t) := Real.sqrt_pos.mpr (by positivity)
  have hz : 0 < (‖x‖ / Real.sqrt (4 * t)) ^ 2 :=
    pow_pos (div_pos (norm_pos_iff.mpr hx) hs) 2
  rw [heatKernel_eq_scaled_profile n ht x]
  exact mul_le_mul_of_nonneg_left (heatMajorantProfile_majorizes n hn hroot hz)
    (heatMajorantNormalization_pos n ht).le

/-- The scaled Poisson tangent dominates the actual Poisson kernel off its singular center. -/
theorem poissonKernel_le_majorant (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    poissonKernel n t x ≤ poissonKernelMajorant n a t x := by
  have hz : 0 < (‖x‖ / t) ^ 2 := pow_pos (div_pos (norm_pos_iff.mpr hx) ht) 2
  rw [poissonKernel_eq_scaled_profile n ht x]
  exact mul_le_mul_of_nonneg_left (poissonMajorantProfile_majorizes n hn hroot hz)
    (poissonMajorantNormalization_pos n ht).le

theorem heatKernel_le_majorant_ae (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsHeatTangencyParameter n a) (ht : 0 < t) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin n), heatKernel n t x ≤ heatKernelMajorant n a t x := by
  have : NeZero n := ⟨by omega⟩
  filter_upwards [volume.ae_ne (0 : EuclideanSpace ℝ (Fin n))] with x hx
  exact heatKernel_le_majorant n hn hroot ht x hx

theorem poissonKernel_le_majorant_ae (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (ht : 0 < t) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      poissonKernel n t x ≤ poissonKernelMajorant n a t x := by
  have : NeZero n := ⟨by omega⟩
  filter_upwards [volume.ae_ne (0 : EuclideanSpace ℝ (Fin n))] with x hx
  exact poissonKernel_le_majorant n hn hroot ht x hx

/-- The normalized heat majorant has an integrable pairing with every compact density. -/
theorem integrable_heatKernelMajorant_mul_compact (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsHeatTangencyParameter n a) (ht : 0 < t)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g)
    (hgsupp : HasCompactSupport g) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ heatKernelMajorant n a t (y - x) * g y) := by
  have hi := integrable_scaled_radial_mul_compact n (fun r ↦ heatMajorantProfile n a (r ^ 2))
    (fun g hg hgsupp ↦ by
      simpa only [sub_zero] using integrable_heatMajorantProfile_mul_compact n hn hroot
        g hg hgsupp 0) g hg hgsupp x (Real.sqrt_pos.mpr (by positivity : 0 < 4 * t))
  convert hi.const_mul (heatMajorantNormalization n t) using 1
  funext y
  unfold heatKernelMajorant
  ring

/-- The normalized Poisson majorant has an integrable pairing with every compact density. -/
theorem integrable_poissonKernelMajorant_mul_compact (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (ht : 0 < t)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g)
    (hgsupp : HasCompactSupport g) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ poissonKernelMajorant n a t (y - x) * g y) := by
  have hi := integrable_scaled_radial_mul_compact n
    (fun r ↦ poissonMajorantProfile n a (r ^ 2)) (fun g hg hgsupp ↦ by
      simpa only [sub_zero] using integrable_poissonMajorantProfile_mul_compact n hn hroot
        g hg hgsupp 0) g hg hgsupp x ht
  convert hi.const_mul (poissonMajorantNormalization n t) using 1
  funext y
  unfold poissonKernelMajorant
  ring

/-- The normalized heat majorant preserves the zero-contact Laplacian comparison. -/
theorem heatKernelMajorant_laplacian_pairing_nonneg (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsHeatTangencyParameter n a) (ht : 0 < t)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (hwpos : ∀ y, 0 ≤ w y)
    (x : EuclideanSpace ℝ (Fin n)) (hx : w x = 0) :
    0 ≤ ∫ y, heatKernelMajorant n a t (y - x) * Laplacian.laplacian w y := by
  have hi := scaled_radial_laplacian_pairing_nonneg n
    (fun r ↦ heatMajorantProfile n a (r ^ 2)) (fun v hv hvsupp hvpos hv0 ↦ by
      simpa only [sub_zero] using heatMajorantProfile_laplacian_pairing_nonneg n hn hroot
        v hv hvsupp hvpos 0 hv0) w hw hsupp hwpos x hx
        (Real.sqrt_pos.mpr (by positivity : 0 < 4 * t))
  have heq : (fun y ↦ heatKernelMajorant n a t (y - x) * Laplacian.laplacian w y) =
      (fun y ↦ heatMajorantNormalization n t *
        (heatMajorantProfile n a ((‖y - x‖ / Real.sqrt (4 * t)) ^ 2) *
          Laplacian.laplacian w y)) := by
    funext y
    unfold heatKernelMajorant
    ring
  rw [heq, integral_const_mul]
  exact mul_nonneg (heatMajorantNormalization_pos n ht).le hi

/-- The normalized Poisson majorant preserves the zero-contact Laplacian comparison. -/
theorem poissonKernelMajorant_laplacian_pairing_nonneg (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (ht : 0 < t)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (hwpos : ∀ y, 0 ≤ w y)
    (x : EuclideanSpace ℝ (Fin n)) (hx : w x = 0) :
    0 ≤ ∫ y, poissonKernelMajorant n a t (y - x) * Laplacian.laplacian w y := by
  have hi := scaled_radial_laplacian_pairing_nonneg n
    (fun r ↦ poissonMajorantProfile n a (r ^ 2)) (fun v hv hvsupp hvpos hv0 ↦ by
      simpa only [sub_zero] using poissonMajorantProfile_laplacian_pairing_nonneg n hn hroot
        v hv hvsupp hvpos 0 hv0) w hw hsupp hwpos x hx ht
  have heq : (fun y ↦ poissonKernelMajorant n a t (y - x) * Laplacian.laplacian w y) =
      (fun y ↦ poissonMajorantNormalization n t *
        (poissonMajorantProfile n a ((‖y - x‖ / t) ^ 2) * Laplacian.laplacian w y)) := by
    funext y
    unfold poissonKernelMajorant
    ring
  rw [heq, integral_const_mul]
  exact mul_nonneg (poissonMajorantNormalization_pos n ht).le hi

end PartialBalayage
