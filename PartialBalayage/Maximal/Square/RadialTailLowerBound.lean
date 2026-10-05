/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RadialTailKernel

/-!
# Genuine finite incoming-tail lower bounds

The actual improper incoming integral dominates every finite rational
polynomial obtained by integrating its genuine binomial truncation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace PartialBalayage.Maximal.Square

/-- The exact finite rational incoming-tail polynomial used by the arithmetic certificate. -/
def radialIncomingPolynomial (R r d : ℝ) (N : ℕ) : ℝ :=
  R ^ (-12 / 5 : ℝ) * ∑ n ∈ Finset.range N, (radialIncomingCoefficient n : ℝ) *
    (2 * (r / R) ^ n + (d / R) ^ n + (-d / R) ^ n)

/-- An individual finite lower monomial of the actual incoming integrand. -/
def radialIncomingMonomial (R r d : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  (radialTailBinomialCoefficient n : ℝ) * (2 * r ^ n + d ^ n + (-d) ^ n) *
    ((R ^ (-6 / 5 : ℝ) - q ^ (-6 / 5 : ℝ)) * q ^ (-11 / 5 - (n : ℝ)))

theorem integrableOn_radialIncomingMonomial {R : ℝ} (hR : 0 < R) (r d : ℝ)
    (n : ℕ) : IntegrableOn (radialIncomingMonomial R r d n) (Ioi R) := by
  have hi := (integrableOn_radial_tail_moment hR (by norm_num : (0 : ℝ) < 6 / 5)
    (Nat.cast_nonneg n)).const_mul
      ((radialTailBinomialCoefficient n : ℝ) * (2 * r ^ n + d ^ n + (-d) ^ n))
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioi
  intro q _
  change (radialTailBinomialCoefficient n : ℝ) * (2 * r ^ n + d ^ n + (-d) ^ n) *
    ((R ^ (-(6 / 5 : ℝ)) - q ^ (-(6 / 5 : ℝ))) *
      q ^ (-(6 / 5 : ℝ) - 1 - (n : ℝ))) = radialIncomingMonomial R r d n q
  simp only [radialIncomingMonomial, show -(6 / 5 : ℝ) = -6 / 5 by ring,
    show (-6 / 5 : ℝ) - 1 - (n : ℝ) = -11 / 5 - (n : ℝ) by ring]

/-- The actual integral of each incoming monomial equals its exact rational coefficient. -/
theorem integral_radialIncomingMonomial {R : ℝ} (hR : 0 < R) (r d : ℝ) (n : ℕ) :
    (∫ q in Ioi R, radialIncomingMonomial R r d n q) =
      R ^ (-12 / 5 : ℝ) * (radialIncomingCoefficient n : ℝ) *
        (2 * (r / R) ^ n + (d / R) ^ n + (-d / R) ^ n) := by
  unfold radialIncomingMonomial
  rw [integral_const_mul]
  have hm := integral_radial_tail_moment hR (by norm_num : (0 : ℝ) < 6 / 5)
    (Nat.cast_nonneg n)
  have he : (-6 / 5 : ℝ) - 1 - (n : ℝ) = -11 / 5 - (n : ℝ) := by ring
  have he₂ : -2 * (6 / 5 : ℝ) - (n : ℝ) = -12 / 5 - (n : ℝ) := by ring
  simp only [show -(6 / 5 : ℝ) = -6 / 5 by ring, he, he₂,
    show 2 * (6 / 5 : ℝ) = 12 / 5 by ring] at hm
  rw [hm]
  simp only [radialIncomingCoefficient, Rat.cast_div, Rat.cast_mul,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat]
  have hp : R ^ (-12 / 5 : ℝ) *
      (2 * (r / R) ^ n + (d / R) ^ n + (-d / R) ^ n) =
      (2 * r ^ n + d ^ n + (-d) ^ n) * R ^ (-12 / 5 - (n : ℝ)) := by
    calc
      _ = 2 * (R ^ (-12 / 5 : ℝ) * (r / R) ^ n) +
          R ^ (-12 / 5 : ℝ) * (d / R) ^ n +
          R ^ (-12 / 5 : ℝ) * (-d / R) ^ n := by ring
      _ = _ := by
        rw [rpow_mul_div_nat hR r, rpow_mul_div_nat hR d, rpow_mul_div_nat hR (-d)]
        ring
  calc
    _ = ((radialTailBinomialCoefficient n : ℝ) * (6 / 5) /
        ((6 / 5 + (n : ℝ)) * (12 / 5 + (n : ℝ)))) *
        ((2 * r ^ n + d ^ n + (-d) ^ n) * R ^ (-12 / 5 - (n : ℝ))) := by ring
    _ = ((radialTailBinomialCoefficient n : ℝ) * (6 / 5) /
        ((6 / 5 + (n : ℝ)) * (12 / 5 + (n : ℝ)))) *
        (R ^ (-12 / 5 : ℝ) *
          (2 * (r / R) ^ n + (d / R) ^ n + (-d / R) ^ n)) := by rw [hp]
    _ = _ := by ring

/-- Integrating the genuine kernel lower bound proves the actual finite tail inequality. -/
theorem radialIncomingPolynomial_le_tail {R r d : ℝ} (hR : 0 < R) (hr : 0 ≤ r)
    (hrR : r < R) (hdR : |d| < R) (N : ℕ) :
    radialIncomingPolynomial R r d N ≤ radialIncomingTail (6 / 5) R r d := by
  have hi : IntegrableOn
      (fun q ↦ ∑ n ∈ Finset.range N, radialIncomingMonomial R r d n q) (Ioi R) :=
    integrable_finsetSum _ (fun n _ ↦ integrableOn_radialIncomingMonomial hR r d n)
  have hK := integrableOn_radialIncomingTail_integrand hR hrR hdR
  have hle := integral_mono_ae hi hK (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    have hqpos := hR.trans hq
    have hw : 0 ≤ R ^ (-6 / 5 : ℝ) - q ^ (-6 / 5 : ℝ) :=
      sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hR hq.le (by norm_num))
    have hb := mul_le_mul_of_nonneg_left
      (radialIncomingPowerKernel_ge_sum hqpos hr (hrR.trans hq) (hdR.trans hq) N) hw
    convert hb using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    unfold radialIncomingMonomial
    ring)
  rw [integral_finsetSum _ (fun n _ ↦ integrableOn_radialIncomingMonomial hR r d n)] at hle
  simp only [integral_radialIncomingMonomial hR r d] at hle
  simp only [mul_assoc] at hle
  rw [← Finset.mul_sum] at hle
  rw [radialIncomingTail_eq_integral_powerKernel]
  exact hle

end PartialBalayage.Maximal.Square
