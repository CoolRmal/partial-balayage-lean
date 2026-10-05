/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.HessianDerivative
public import PartialBalayage.Linear.SobolevUnivDensity
public import PartialBalayage.Linear.SobolevDistributionGradient
public import PartialBalayage.Linear.SecondSobolevZeroSet

/-!
# Genuine global Hessian graphs and zero-set locality

Fourier order-two regularity constructs actual whole-space H01 graphs for all first
derivatives, using the proved density of compact smooth graphs. The actual Hessian Fourier
operator of a Laplace forcing is their represented second derivative. Applying Sobolev
zero-set locality twice therefore proves that the full complex Hessian vanishes on the
state zero set. No second-gradient membership or operator cancellation is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter TemperedDistribution
open CenteredMaximal.Ball.DirichletSobolev
open scoped SchwartzMap Laplacian LineDeriv

namespace PartialBalayage.Linear

variable {d : ℕ}

/-- The genuine L² embedding into tempered distributions is injective. -/
theorem L2_eq_of_tempered_eq
    (a b : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (heq : (a : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (b : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) : a = b := by
  have hinj : Function.Injective (Lp.toTemperedDistributionCLM ℂ
      (volume : Measure (EuclideanSpace ℝ (Fin d))) 2) :=
    LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
  exact hinj heq

/-- Global order-two regularity of an actual H01 state constructs its genuine iterated
H01 gradient graphs. The graph membership is a conclusion. -/
theorem exists_secondGradientGraph_H01_of_memSobolev_two
    (U : H01 (univ : Set (EuclideanSpace ℝ (Fin d))))
    (hu : MemSobolev 2 2
      (complexGlobalGraphCoordinateCLM (d := d) 0 (U : H1amb univ) :
        𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) :
    ∃ G : Fin d → H01 (univ : Set (EuclideanSpace ℝ (Fin d))),
      IsSecondGradientGraph U G := by
  let g (i : Fin d) := complexGlobalGraphCoordinateCLM (d := d) i.succ (U : H1amb univ)
  have hg (i : Fin d) : MemSobolev 1 2
      (g i : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
    rw [show (g i : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      ∂_{EuclideanSpace.single i (1 : ℝ)}
        (complexGlobalGraphCoordinateCLM (d := d) 0 (U : H1amb univ) :
          𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) from
            (lineDeriv_complexGlobalGraphCoordinate_H01 U i).symm]
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      hu.lineDerivOp (m := EuclideanSpace.single i (1 : ℝ))
  let W (i : Fin d) := fourierSobolevRealGraph (g i) (hg i)
  let G (i : Fin d) : H01 (univ : Set (EuclideanSpace ℝ (Fin d))) :=
    ⟨(W i).val, mem_H01_univ_of_mem_W12 (W i).property⟩
  refine ⟨G, fun i ↦ ?_⟩
  have hvalue : (G i).val 0 =ᵐ[volume] fun x ↦ U.val i.succ x := by
    filter_upwards [complexL2GradientGraph_value_ae (g i) (sobolevL2Partial (g i) (hg i)),
      complexGlobalGraphCoordinateCLM_ae i.succ (U : H1amb univ)] with x hw hcomplex
    change complexL2GradientGraph (g i) (sobolevL2Partial (g i) (hg i)) 0 x = _
    rw [hw]
    change (complexGlobalGraphCoordinateCLM (d := d) i.succ (U : H1amb univ) x : ℂ).re = _
    rw [hcomplex, Complex.ofReal_re]
  simpa only [Filter.EventuallyEq, Measure.restrict_univ] using hvalue

/-- The actual Hessian matrix entries are the complexifications of genuine second graph
coordinates; this proves reality as well as identifying their weak derivatives. -/
theorem hessianEntry_eq_complex_secondGradientGraph
    (U : H01 (univ : Set (EuclideanSpace ℝ (Fin d))))
    (q : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hΔ : Δ (complexGlobalGraphCoordinateCLM (d := d) 0 (U : H1amb univ) :
        𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      -(q : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)))
    (G : Fin d → H01 (univ : Set (EuclideanSpace ℝ (Fin d))))
    (hG : IsSecondGradientGraph U G) (i j : Fin d) :
    (hessianEntryCLM i j).compLp (hessianL2 q) =
      complexGlobalGraphCoordinateCLM (d := d) j.succ (G i : H1amb univ) := by
  have hvalue : complexGlobalGraphCoordinateCLM (d := d) 0 (G i : H1amb univ) =
      complexGlobalGraphCoordinateCLM (d := d) i.succ (U : H1amb univ) := by
    apply Lp.ext
    have hGi : (G i).val 0 =ᵐ[volume] U.val i.succ := by
      simpa only [Measure.restrict_univ, Filter.EventuallyEq] using hG i
    filter_upwards [complexGlobalGraphCoordinateCLM_ae 0 (G i : H1amb univ),
      complexGlobalGraphCoordinateCLM_ae i.succ (U : H1amb univ), hGi]
      with x hleft hright hx
    rw [hleft, hright, hx]
  apply L2_eq_of_tempered_eq
  let u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    complexGlobalGraphCoordinateCLM (d := d) 0 (U : H1amb univ)
  have hΔu : Δ (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      -(q : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := hΔ
  have hentry := @hessianEntry_represents_second_derivative d u q hΔu i j
  have hfirst := (lineDeriv_complexGlobalGraphCoordinate_H01 U i).trans
    (congrArg (fun a : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) ↦
      (a : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) hvalue.symm)
  exact hentry.symm.trans ((congrArg (fun T : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ) ↦
    ∂_{EuclideanSpace.single j (1 : ℝ)} T) hfirst).trans
      (lineDeriv_complexGlobalGraphCoordinate_H01 (G i) j))

/-- A genuine L² Laplace equation forces the full Hessian Fourier operator to vanish
almost everywhere on the actual H01 state's value zero set. -/
theorem ae_hessianL2_eq_zero_on_H01_value_zero_of_laplace_equation
    (U : H01 (univ : Set (EuclideanSpace ℝ (Fin d))))
    (q : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hΔ : Δ (complexGlobalGraphCoordinateCLM (d := d) 0 (U : H1amb univ) :
        𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      -(q : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) :
    ∀ᵐ x ∂volume, U.val 0 x = 0 → hessianL2 q x = 0 := by
  have hu : MemSobolev 2 2
      (complexGlobalGraphCoordinateCLM (d := d) 0 (U : H1amb univ) :
        𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
    apply memSobolev_two_of_L2_laplacian _ (-q)
    simpa only [← Lp.toTemperedDistributionCLM_apply, map_neg] using hΔ
  obtain ⟨G, hG⟩ := exists_secondGradientGraph_H01_of_memSobolev_two U hu
  have hlocal : ∀ᵐ x ∂volume, U.val 0 x = 0 →
      ∀ i j : Fin d, (G i).val j.succ x = 0 := by
    simpa only [Measure.restrict_univ] using
      ae_all_second_gradients_eq_zero_on_value_zero isOpen_univ U G hG
  have hentry (i j : Fin d) : ∀ᵐ x ∂volume,
      hessianL2 q x (i, j) = ((G i).val j.succ x : ℂ) := by
    have heq := hessianEntry_eq_complex_secondGradientGraph U q hΔ G hG i j
    have hae := (hessianEntryCLM i j).coeFn_compLp (hessianL2 q)
    rw [heq] at hae
    filter_upwards [hae, complexGlobalGraphCoordinateCLM_ae j.succ (G i : H1amb univ)]
      with x hx hcomplex
    exact hx.symm.trans hcomplex
  have hall : ∀ᵐ x ∂volume, ∀ i j : Fin d,
      hessianL2 q x (i, j) = ((G i).val j.succ x : ℂ) :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ hentry i j
  filter_upwards [hlocal, hall] with x hzero hx
  intro hu0
  ext ij
  rw [hx ij.1 ij.2, hzero hu0 ij.1 ij.2]
  simp

end PartialBalayage.Linear
