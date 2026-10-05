/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.ScaledSemigroupMajorants
public import PartialBalayage.Maximal.SquaredRadialMass

/-!
# Full Euclidean masses of the heat and Poisson majorants

The harmonic inner profiles are integrated with their actual radial weight. Their outer tails
are integrable, and squared-radius polar integration and positive dilation give the article's
exact Gamma formulas. Mass calculations require positive parameters; kernel admissibility uses
the separately proved exact tangency equations.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PartialBalayage.Constants

namespace PartialBalayage

private theorem split_profile_core_ae (b : ℝ) (p q : ℝ → ℝ) :
    p =ᵐ[volume.restrict (Ioc 0 b)] fun z ↦ if z < b then p z else q z := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne b)] with z hz hzb
  simp only [ite_eq_left (lt_of_le_of_ne hz.2 hzb)]

private theorem integrable_split_profile {b : ℝ} (hb : 0 < b) {p q : ℝ → ℝ}
    (hp : IntervalIntegrable p volume 0 b) (hq : IntegrableOn q (Ioi b)) :
    IntegrableOn (fun z ↦ if z < b then p z else q z) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi hb.le, integrableOn_union]
  constructor
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp hp).congr
      (split_profile_core_ae b p q)
  · apply hq.congr_fun _ measurableSet_Ioi
    intro z hz
    simp only [ite_eq_right (not_lt_of_gt hz)]

private theorem integral_split_profile {b : ℝ} (hb : 0 < b) {p q : ℝ → ℝ}
    (hp : IntervalIntegrable p volume 0 b) (hq : IntegrableOn q (Ioi b)) :
    (∫ z in Ioi (0 : ℝ), if z < b then p z else q z) =
      (∫ z in 0..b, p z) + ∫ z in Ioi b, q z := by
  have hcore := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp hp).congr
    (split_profile_core_ae b p q)
  have htail : IntegrableOn (fun z ↦ if z < b then p z else q z) (Ioi b) := by
    apply hq.congr_fun _ measurableSet_Ioi
    intro z hz
    simp only [ite_eq_right (not_lt_of_gt hz)]
  rw [← Ioc_union_Ioi_eq_Ioi hb.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hcore htail]
  congr 1
  · rw [intervalIntegral.integral_of_le hb.le]
    exact integral_congr_ae (split_profile_core_ae b p q).symm
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    simp only [ite_eq_right (not_lt_of_gt hz)]

private theorem integrable_weighted_heat_tail (n : ℕ) (hn : 1 ≤ n) {b : ℝ}
    (hb : 0 < b) :
    IntegrableOn (fun z ↦ Real.exp (-z) * z ^ ((n : ℝ) / 2 - 1)) (Ioi b) := by
  have hβ : 0 < (n : ℝ) / 2 := div_pos
    (by exact_mod_cast (show 0 < n by omega)) (by norm_num)
  exact (Real.GammaIntegral_convergent hβ).mono_set (Ioi_subset_Ioi hb.le)

private theorem integrable_weighted_poisson_tail (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun z ↦ (1 + z) ^ (-(((n : ℝ) + 1) / 2)) *
      z ^ ((n : ℝ) / 2 - 1)) (Ioi b) := by
  apply (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) hb).mono'
    (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hzpos : 0 < z := hb.trans hz
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ z ^ (-(((n : ℝ) + 1) / 2)) * z ^ ((n : ℝ) / 2 - 1) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hzpos.le _)
      exact Real.rpow_le_rpow_of_nonpos hzpos (by linarith)
        (by linarith [Nat.cast_nonneg (α := ℝ) n])
    _ = z ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hzpos]
      congr 1
      ring

private theorem intervalIntegrable_weighted_heat_tangent (n : ℕ) (hn : 1 ≤ n)
    {a : ℝ} (ha : 0 < a) :
    IntervalIntegrable (fun z ↦ heatHarmonicTangent n a z *
      z ^ ((n : ℝ) / 2 - 1)) volume 0 (rho n * a) := by
  apply intervalIntegral.intervalIntegrable_of_integral_ne_zero
  rw [integral_weighted_heatHarmonicTangent n hn ha]
  have hb := mul_pos (rho_pos n hn) ha
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  exact (by positivity : 0 < 2 * (rho n * a) ^ ((n : ℝ) / 2) *
    Real.exp (-a) / (n : ℝ)).ne'

private theorem intervalIntegrable_weighted_poisson_tangent (n : ℕ) (hn : 1 ≤ n)
    {a : ℝ} (ha : 0 < a) :
    IntervalIntegrable (fun z ↦ poissonHarmonicTangent n a z *
      z ^ ((n : ℝ) / 2 - 1)) volume 0 (rho n * a) := by
  apply intervalIntegral.intervalIntegrable_of_integral_ne_zero
  rw [integral_weighted_poissonHarmonicTangent n hn ha]
  have hb := mul_pos (rho_pos n hn) ha
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  exact (by positivity : 0 < 2 * (rho n * a) ^ ((n : ℝ) / 2) *
    (1 + a) ^ (-(((n : ℝ) + 1) / 2)) / (n : ℝ)).ne'

/-- The heat majorant profile is integrable against the actual radial Gamma weight. -/
theorem integrable_weighted_heatMajorantProfile (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha : 0 < a) :
    IntegrableOn (fun z ↦ heatMajorantProfile n a z * z ^ ((n : ℝ) / 2 - 1)) (Ioi 0) := by
  simpa only [heatMajorantProfile, ite_mul] using
    integrable_split_profile (mul_pos (rho_pos n hn) ha)
      (intervalIntegrable_weighted_heat_tangent n hn ha)
      (integrable_weighted_heat_tail n hn (mul_pos (rho_pos n hn) ha))

/-- The Poisson majorant profile is integrable against the actual radial Gamma weight. -/
theorem integrable_weighted_poissonMajorantProfile (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha : 0 < a) :
    IntegrableOn (fun z ↦ poissonMajorantProfile n a z *
      z ^ ((n : ℝ) / 2 - 1)) (Ioi 0) := by
  simpa only [poissonMajorantProfile, ite_mul] using
    integrable_split_profile (mul_pos (rho_pos n hn) ha)
      (intervalIntegrable_weighted_poisson_tangent n hn ha)
      (integrable_weighted_poisson_tail n (mul_pos (rho_pos n hn) ha))

/-- The complete weighted heat profile has the exact inner mass plus its Gamma tail. -/
theorem integral_weighted_heatMajorantProfile (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha : 0 < a) :
    (∫ z in Ioi (0 : ℝ), heatMajorantProfile n a z * z ^ ((n : ℝ) / 2 - 1)) =
      2 * (rho n * a) ^ ((n : ℝ) / 2) * Real.exp (-a) / (n : ℝ) +
        ∫ z in Ioi (rho n * a), z ^ ((n : ℝ) / 2 - 1) * Real.exp (-z) := by
  simp only [heatMajorantProfile, ite_mul]
  rw [integral_split_profile (mul_pos (rho_pos n hn) ha)
    (intervalIntegrable_weighted_heat_tangent n hn ha)
    (integrable_weighted_heat_tail n hn (mul_pos (rho_pos n hn) ha)),
    integral_weighted_heatHarmonicTangent n hn ha]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro z hz
  ring

/-- The complete weighted Poisson profile has the exact inner mass plus its outer tail. -/
theorem integral_weighted_poissonMajorantProfile (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha : 0 < a) :
    (∫ z in Ioi (0 : ℝ), poissonMajorantProfile n a z * z ^ ((n : ℝ) / 2 - 1)) =
      2 * (rho n * a) ^ ((n : ℝ) / 2) /
        ((n : ℝ) * (1 + a) ^ (((n : ℝ) + 1) / 2)) +
        ∫ z in Ioi (rho n * a),
          z ^ ((n : ℝ) / 2 - 1) / (1 + z) ^ (((n : ℝ) + 1) / 2) := by
  simp only [poissonMajorantProfile, ite_mul]
  rw [integral_split_profile (mul_pos (rho_pos n hn) ha)
    (intervalIntegrable_weighted_poisson_tangent n hn ha)
    (integrable_weighted_poisson_tail n (mul_pos (rho_pos n hn) ha)),
    integral_weighted_poissonHarmonicTangent n hn ha,
    Real.rpow_neg (by positivity : 0 ≤ 1 + a)]
  congr 1
  · ring
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    have hzpos : 0 < z := (mul_pos (rho_pos n hn) ha).trans hz
    change (1 + z) ^ (-(((n : ℝ) + 1) / 2)) * z ^ ((n : ℝ) / 2 - 1) =
      z ^ ((n : ℝ) / 2 - 1) / (1 + z) ^ (((n : ℝ) + 1) / 2)
    rw [Real.rpow_neg (by positivity : 0 ≤ 1 + z)]
    ring

/-- The heat majorant is integrable in the full ambient Euclidean space. -/
theorem integrable_heatKernelMajorant (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) : Integrable (heatKernelMajorant n a t) := by
  exact (integrable_scaled_radial_square n hn (integrable_weighted_heatMajorantProfile n hn ha)
    (Real.sqrt_pos.mpr (by positivity : 0 < 4 * t))).const_mul
      (heatMajorantNormalization n t)

/-- The Poisson majorant is integrable in the full ambient Euclidean space. -/
theorem integrable_poissonKernelMajorant (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) : Integrable (poissonKernelMajorant n a t) := by
  exact (integrable_scaled_radial_square n hn
    (integrable_weighted_poissonMajorantProfile n hn ha) ht).const_mul
      (poissonMajorantNormalization n t)

private theorem heatMajorant_normalization_mass (n : ℕ) (hn : 1 ≤ n) {t : ℝ}
    (ht : 0 < t) :
    heatMajorantNormalization n t * (Real.sqrt (4 * t)) ^ n *
      (Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) =
        (Real.Gamma ((n : ℝ) / 2))⁻¹ := by
  have hbase : 0 < 4 * t := by positivity
  have hs : (Real.sqrt (4 * t)) ^ n = (4 * t) ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    congr 1
    ring
  have hπ := (Real.rpow_pos_of_pos Real.pi_pos ((n : ℝ) / 2)).ne'
  have hscale := (Real.rpow_pos_of_pos hbase ((n : ℝ) / 2)).ne'
  have hΓ := (Real.Gamma_pos_of_pos (show 0 < (n : ℝ) / 2 from div_pos
    (by exact_mod_cast (show 0 < n by omega)) (by norm_num))).ne'
  unfold heatMajorantNormalization
  rw [show 4 * Real.pi * t = Real.pi * (4 * t) by ring,
    show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring,
    Real.mul_rpow Real.pi_nonneg hbase.le, Real.rpow_neg Real.pi_nonneg,
    Real.rpow_neg hbase.le, hs]
  field_simp

private theorem poissonMajorant_normalization_mass (n : ℕ) (hn : 1 ≤ n) {t : ℝ}
    (ht : 0 < t) :
    poissonMajorantNormalization n t * t ^ n *
      (Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) =
        Real.Gamma (((n : ℝ) + 1) / 2) /
          (Real.sqrt Real.pi * Real.Gamma ((n : ℝ) / 2)) := by
  have hπ : Real.pi ^ (((n : ℝ) + 1) / 2) =
      Real.pi ^ ((n : ℝ) / 2) * Real.sqrt Real.pi := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  have hπpow := (Real.rpow_pos_of_pos Real.pi_pos ((n : ℝ) / 2)).ne'
  have hsqrt := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hscale := (Real.rpow_pos_of_pos ht (n : ℝ)).ne'
  have hΓ := (Real.Gamma_pos_of_pos (show 0 < (n : ℝ) / 2 from div_pos
    (by exact_mod_cast (show 0 < n by omega)) (by norm_num))).ne'
  unfold poissonMajorantNormalization
  rw [Real.rpow_neg ht.le, ← Real.rpow_natCast, hπ]
  field_simp

/-- The full heat-majorant mass equals the article's exact bound formula at `b = ρₙa`. -/
theorem integral_heatKernelMajorant (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ (Fin n), heatKernelMajorant n a t x) =
      heatBoundFormula n a (rho n * a) := by
  unfold heatKernelMajorant
  rw [integral_const_mul, integral_scaled_radial_square n hn (heatMajorantProfile n a)
    (Real.sqrt_pos.mpr (by positivity : 0 < 4 * t)), ← mul_assoc, ← mul_assoc,
    heatMajorant_normalization_mass n hn ht, integral_weighted_heatMajorantProfile n hn ha]
  rfl

/-- The full Poisson-majorant mass equals the article's exact bound formula at `b = ρₙa`. -/
theorem integral_poissonKernelMajorant (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ (Fin n), poissonKernelMajorant n a t x) =
      poissonBoundFormula n a (rho n * a) := by
  unfold poissonKernelMajorant
  rw [integral_const_mul, integral_scaled_radial_square n hn (poissonMajorantProfile n a) ht,
    ← mul_assoc, ← mul_assoc, poissonMajorant_normalization_mass n hn ht,
    integral_weighted_poissonMajorantProfile n hn ha]
  rfl

/-- The admissible heat majorant has the exact nonnegative Lebesgue mass from the table. -/
theorem lintegral_heatKernelMajorant (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsHeatTangencyParameter n a) (ht : 0 < t) :
    (∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (heatKernelMajorant n a t x)) =
      ENNReal.ofReal (heatBoundFormula n a (rho n * a)) := by
  have hρ := rho_pos n hn
  have ha : 0 < a := lt_of_le_of_lt (by positivity) hroot.1.1
  have hnonneg : 0 ≤ᵐ[volume] heatKernelMajorant n a t := by
    filter_upwards [heatKernel_le_majorant_ae n hn hroot ht] with x hx
    exact (heatKernel_pos n ht x).le.trans hx
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernelMajorant n hn ha ht)
    hnonneg, integral_heatKernelMajorant n hn ha ht]

/-- The admissible Poisson majorant has the exact nonnegative Lebesgue mass from the table. -/
theorem lintegral_poissonKernelMajorant (n : ℕ) (hn : 1 ≤ n) {a t : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (ht : 0 < t) :
    (∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (poissonKernelMajorant n a t x)) =
      ENNReal.ofReal (poissonBoundFormula n a (rho n * a)) := by
  have hρ := rho_pos n hn
  have ha : 0 < a := lt_of_le_of_lt (by positivity) hroot.1.1
  have hnonneg : 0 ≤ᵐ[volume] poissonKernelMajorant n a t := by
    filter_upwards [poissonKernel_le_majorant_ae n hn hroot ht] with x hx
    exact (poissonKernel_pos n ht x).le.trans hx
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_poissonKernelMajorant n hn ha ht)
    hnonneg, integral_poissonKernelMajorant n hn ha ht]

end PartialBalayage
