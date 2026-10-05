/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.PoissonL2

/-!
# Real-linear transport of genuine Poisson averaging

Actual normalized spatial convolution commutes with any bounded real-linear output map.
This includes complexification and real or imaginary coordinate extraction.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PartialBalayage.Linear

variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

local notation "D" => EuclideanSpace ℝ (Fin n)

/-- Actual Poisson `L²` averaging commutes with bounded real-linear postcomposition. -/
theorem poissonConvolutionL2_compLp {t : ℝ} (ht : 0 < t) (L : E →L[ℝ] F)
    (f : Lp E 2 (volume : Measure D)) :
    poissonConvolutionL2 ht (L.compLp f) = L.compLp (poissonConvolutionL2 ht f) := by
  have hsource := poissonConvolution_congr t (L.coeFn_compLp f)
  apply Lp.ext
  filter_upwards [poissonConvolutionL2_ae ht (L.compLp f),
    L.coeFn_compLp (poissonConvolutionL2 ht f), poissonConvolutionL2_ae ht f,
    ae_integrable_poisson_translates ht f] with x hP hL hPf hint
  rw [hP, hL, hPf, hsource]
  change (∫ y, L (f (x - y)) ∂(PartialBalayage.poissonKernelMeasure n t)) =
    L (∫ y, f (x - y) ∂(PartialBalayage.poissonKernelMeasure n t))
  exact L.integral_comp_comm hint

end PartialBalayage.Linear
