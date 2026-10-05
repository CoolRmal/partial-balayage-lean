/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RationalInterval
public import PartialBalayage.Maximal.Square.Kernel

/-!
# Exact rational generator scale enclosures

The literal endpoints are candidate fifth-root bounds. Their fifth-power checks
are proved by ordinary Lean kernel reduction before being connected to the actual
radial and spline scale factors.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Candidate enclosure of the actual incoming-tail radius factor. -/
def generatorRadiusInterval : RationalInterval := ⟨
  (330908748841216501915545921253 / 1267650600228229401496703205376 : ℚ),
  (165454374420608250957772960627 / 633825300114114700748351602688 : ℚ)⟩

/-- Both endpoints enclose the actual fifth-root power by exact rational arithmetic. -/
theorem generatorRadiusInterval_valid :
    IsPowerEnclosure (7 / 4) (-12) generatorRadiusInterval.lower
      generatorRadiusInterval.upper := by
  unfold IsPowerEnclosure generatorRadiusInterval
  decide +kernel

/-- Candidate enclosure of the actual inverse mesh power. -/
def generatorMeshInterval : RationalInterval := ⟨
  (35313726210923359253896589521535 / 1267650600228229401496703205376 : ℚ),
  (275888486022838744171067105637 / 9903520314283042199192993792 : ℚ)⟩

/-- Both inverse-mesh endpoints pass the ordinary exact rational fifth-power checks. -/
theorem generatorMeshInterval_valid :
    IsPowerEnclosure (1 / 16) (-6) generatorMeshInterval.lower
      generatorMeshInterval.upper := by
  unfold IsPowerEnclosure generatorMeshInterval
  decide +kernel

/-- The actual positive spline generator prefactor. -/
def splineGeneratorFactor : ℝ := (625 / 216 : ℝ) * (16 : ℝ) ^ (6 / 5 : ℝ)

/-- The exact rational interval obtained by genuine positive scalar multiplication. -/
def splineGeneratorFactorInterval : RationalInterval := generatorMeshInterval.scale (625 / 216)

theorem generatorRadiusInterval_contains :
    generatorRadiusInterval.Contains (supportRadius ^ (-12 / 5 : ℝ)) := by
  have h := generatorRadiusInterval_valid.rpow_bounds (by norm_num : (0 : ℚ) ≤ 7 / 4)
  simpa only [RationalInterval.Contains, supportRadius, Rat.cast_div, Rat.cast_ofNat,
    Int.cast_neg, Int.cast_ofNat] using h

theorem splineGeneratorFactorInterval_contains :
    splineGeneratorFactorInterval.Contains splineGeneratorFactor := by
  have h : generatorMeshInterval.Contains ((1 / 16 : ℝ) ^ (-6 / 5 : ℝ)) := by
    have hp := generatorMeshInterval_valid.rpow_bounds (by norm_num : (0 : ℚ) ≤ 1 / 16)
    simpa only [RationalInterval.Contains, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
      Int.cast_neg, Int.cast_ofNat] using hp
  have hscale := h.scale (625 / 216)
  have he : (1 / 16 : ℝ) ^ (-6 / 5 : ℝ) = (16 : ℝ) ^ (6 / 5 : ℝ) := by
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  simpa only [splineGeneratorFactorInterval, splineGeneratorFactor, Rat.cast_div,
    Rat.cast_ofNat, he] using hscale

theorem splineGeneratorFactorInterval_lower_nonneg : 0 ≤ splineGeneratorFactorInterval.lower := by
  unfold splineGeneratorFactorInterval RationalInterval.scale generatorMeshInterval
  norm_num

theorem splineGeneratorFactor_nonneg : 0 ≤ splineGeneratorFactor := by
  unfold splineGeneratorFactor
  positivity

end PartialBalayage.Maximal.Square
