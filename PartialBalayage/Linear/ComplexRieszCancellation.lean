/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ComplexRieszWeakGradient
public import PartialBalayage.Linear.ComplexGradientZeroSet
public import PartialBalayage.Linear.RieszLinearity

/-!
# Genuine full-vector complex Riesz cancellation

The actual represented first derivatives vanish on the complex potential's zero
set. Applying this to the genuine physical Poisson equation gives agreement of
the full complex Riesz vectors off the constructed active set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal

namespace PartialBalayage.Linear

variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)

/-- The actual full complex Riesz vector vanishes on the physical potential's zero set. -/
theorem ae_complex_rieszL2_eq_zero_on_value_zero (u q : L²ℂ)
    (hPDE : ∀ W : H01 (univ : Set D),
      inner ℂ u (h01PoissonGenerator W) = inner ℂ q (h01ComplexValueCLM W)) :
    ∀ᵐ x, u x = 0 → rieszL2 q x = 0 := by
  have hz := ae_complex_gradient_eq_zero_on_value_zero u
    (fun i ↦ (projectionCoordinateCLM i).compLp (rieszL2 q))
    (complex_rieszCoordinate_represents_first_derivative u q hPDE)
  have hc : ∀ᵐ x, ∀ i : Fin n,
      (projectionCoordinateCLM i).compLp (rieszL2 q) x = rieszL2 q x i :=
    ae_all_iff.mpr (fun i ↦ projectionCoordinateCLM_ae (rieszL2 q) i)
  filter_upwards [hz, hc] with x hx hc
  intro hu
  ext i
  change rieszL2 q x i = 0
  exact (hc i).symm.trans (hx hu i)

/-- The genuine complex physical equation gives full-vector agreement off the active set. -/
theorem complex_riesz_eq_off_of_h01_equation (f ν u : L²ℂ)
    (hPDE : ∀ W : H01 (univ : Set D),
      inner ℂ u (h01PoissonGenerator W) = inner ℂ (f - ν) (h01ComplexValueCLM W))
    {s : Set D} (hzero : ∀ᵐ x, x ∉ s → u x = 0) :
    ∀ᵐ x, x ∉ s → rieszL2CLM n f x = rieszL2CLM n ν x := by
  have hz := ae_complex_rieszL2_eq_zero_on_value_zero u (f - ν) hPDE
  change ∀ᵐ x, u x = 0 → rieszL2CLM n (f - ν) x = 0 at hz
  rw [map_sub] at hz
  filter_upwards [hz, hzero,
    Lp.coeFn_sub (rieszL2CLM n f) (rieszL2CLM n ν)] with x hz hu hs
  intro hx
  exact sub_eq_zero.mp (hs.symm.trans (hz (hu hx)))

end PartialBalayage.Linear
