/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WholeSpaceWeakPDE
public import PartialBalayage.Linear.DirichletTestClosure
public import CenteredMaximal.Ball.LocalWeakPairing

/-!
# The actual distributional equation of the whole-space Dirichlet state

The compact-test PDE supplied by finite-domain exhaustion is converted to the ordinary
local distributional Laplacian identity. The forcing is the density minus the input,
with the sign determined by the actual positive Dirichlet energy pairing.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Ball CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace NNReal

namespace PartialBalayage.Linear

variable {d m : ℕ}

/-- The true compact-test equation of an all-space H01 graph gives its actual raw
distributional Laplacian. No represented second derivatives are assumed. -/
theorem hasLocalDistributionalLaplacian_H01_of_test_equation
    (U : H01 (univ : Set (EuclideanSpace ℝ (Fin d))))
    (g : L2D (univ : Set (EuclideanSpace ℝ (Fin d))))
    (htest : ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : IsTestFn univ φ),
      laplaceBilin univ U hφ.toH01 = inner ℝ g hφ.testCls) :
    HasLocalDistributionalLaplacian d univ
      (fun x ↦ (U : H1amb univ) 0 x) (fun x ↦ -g x) := by
  have heq := laplaceBilin_eq_inner_of_test_equation U g htest
  intro φ hφs hφc hφu
  let hφ : IsTestFn univ φ := ⟨hφc, hφs, hφu⟩
  have h := weak_equation_local_distributional_laplacian U g
    (fun W ↦ by simpa only [l2Functional_apply] using heq W) hφ
  simp only [Measure.restrict_univ] at h
  calc
    (∫ x, φ x * (-g x)) = -(∫ x, g x * φ x) := by
      rw [← integral_neg]
      congr 1
      funext x
      ring
    _ = _ := h.symm

/-- The actual coordinate PDE of a global vector state has forcing `ν - f`. -/
theorem vector_hasLocalDistributionalLaplacian_of_test_equation
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    (f ν : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hpde : ∀ j : Fin m, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ∀ hφ : IsTestFn univ φ,
        laplaceBilin univ (U j) hφ.toH01 =
          inner ℝ (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν)
            hφ.testCls) (j : Fin m) :
    HasLocalDistributionalLaplacian d univ
      (fun x ↦ (U j : H1amb univ) 0 x)
      (fun x ↦ univVectorCoordinateCLM j ν x - univVectorCoordinateCLM j f x) := by
  have h := hasLocalDistributionalLaplacian_H01_of_test_equation (U j)
    (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν) (hpde j)
  intro φ hφs hφc hφu
  rw [← h φ hφs hφc hφu]
  apply integral_congr_ae
  have hae := Lp.coeFn_sub (univVectorCoordinateCLM j f) (univVectorCoordinateCLM j ν)
  simp only [Measure.restrict_univ] at hae
  filter_upwards [hae] with x hx
  rw [hx]
  simp only [Pi.sub_apply]
  ring

/-- Exhaustion therefore constructs genuine capped finite-mass vector densities and
actual H01 states satisfying the raw distributional Laplace equation. -/
theorem exists_wholeSpace_vector_distributional_PDE {n : ℕ}
    (f : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (hf : Integrable (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin m)) volume)
    (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ (ν : Lp (EuclideanSpace ℝ (Fin m)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
      (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin (n + 1)))) m),
      ν ∈ normMassCap volume κ ⟨∫ x, ‖f x‖, integral_nonneg (fun _ ↦ norm_nonneg _)⟩ ∧
      ∀ j : Fin m, HasLocalDistributionalLaplacian (n + 1) univ
        (fun x ↦ (U j : H1amb univ) 0 x)
        (fun x ↦ univVectorCoordinateCLM j ν x - univVectorCoordinateCLM j f x) := by
  obtain ⟨ν, U, hν, hpde⟩ := exists_wholeSpace_vector_weak_PDE f hf κ hκ
  exact ⟨ν, U, hν, vector_hasLocalDistributionalLaplacian_of_test_equation U f ν hpde⟩

end PartialBalayage.Linear
