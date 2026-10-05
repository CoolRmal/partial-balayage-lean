/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.IsotropicSobolevRegularity
public import PartialBalayage.Linear.SobolevUnivDensity
public import PartialBalayage.Linear.FourierDirichletEnergy

/-!
# Actual physical gradient graphs of isotropic first-order states

Genuine Fourier Sobolev regularity constructs the physical real weak-gradient graph.
Whole-space compact approximation places it in the actual Dirichlet closure. If the
original value is real, its complex graph observation is exactly that original class.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal SchwartzMap

namespace PartialBalayage.Linear

variable {n : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "L²ℝ" => Lp ℝ 2 (volume : Measure D)
local notation "L²ℂ" => Lp ℂ 2 (volume : Measure D)
local notation "H¹" => IsotropicEnergySpace (X := D) (E := ℂ) 2

/-- The genuine all-space physical real gradient graph of an actual isotropic state. -/
def isotropicTwoH01 (U : H¹) : H01 (univ : Set D) :=
  ⟨(fourierSobolevRealGraph (isotropicEnergyValue 2 U) (memSobolev_one_isotropicTwo U)).val,
    mem_H01_univ_of_mem_W12
      (fourierSobolevRealGraph (isotropicEnergyValue 2 U)
        (memSobolev_one_isotropicTwo U)).property⟩

/-- Its actual physical value is the real part of the original isotropic value. -/
theorem isotropicTwoH01_value_ae (U : H¹) :
    ((isotropicTwoH01 U : H1amb univ) 0 : D → ℝ) =ᵐ[volume]
      fun x ↦ (isotropicEnergyValue 2 U x).re :=
  complexL2GradientGraph_value_ae (isotropicEnergyValue 2 U) _

/-- If the original state is actually real, its physical graph has exactly that complex value. -/
theorem complexGlobalGraphCoordinate_isotropicTwoH01 (U : H¹) (f : L²ℝ)
    (hU : isotropicEnergyValue 2 U = Complex.ofRealCLM.compLp f) :
    complexGlobalGraphCoordinateCLM 0 (isotropicTwoH01 U : H1amb univ) =
      isotropicEnergyValue 2 U := by
  apply Lp.ext
  filter_upwards [complexGlobalGraphCoordinateCLM_ae 0 (isotropicTwoH01 U : H1amb univ),
    isotropicTwoH01_value_ae U, Complex.ofRealCLM.coeFn_compLp f] with x hc hv hf
  rw [hc, hv, hU, hf]
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_re]

end PartialBalayage.Linear
