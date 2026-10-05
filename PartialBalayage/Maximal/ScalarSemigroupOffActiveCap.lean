/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.ScalarSemigroupContact
public import PartialBalayage.Maximal.KernelContactCap
public import PartialBalayage.Maximal.HeatKernel
public import PartialBalayage.Maximal.PoissonKernel
public import PartialBalayage.Maximal.SemigroupTimeContinuity

/-!
# Concrete heat and Poisson caps outside an actual scalar active set

The exact normalized tangent majorants dominate the original semigroup kernels and have the
article's exact mass. The genuine nonnegative scalar obstacle discharges the distributional
contact condition, and its capped density bounds the original heat and Poisson convolutions.
A final existence theorem assumes only a true nonnegative integrable scalar `L²` input and
positive cap, and supplies one actual state and active set for both semigroups at every time.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open PartialBalayage.Linear PartialBalayage.Constants
open scoped RealInnerProductSpace NNReal ENNReal

namespace PartialBalayage

variable {d : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "ScalarState" => VectorDirichletState (univ : Set X) 1
local notation "VectorL2" => Lp (EuclideanSpace ℝ (Fin 1)) 2 (volume : Measure X)

/-- The actual scalar coordinate of a vector density retains its true `L²` integrability. -/
theorem memLp_scalarCoordinate (f : VectorL2) : MemLp (fun x ↦ f x 0) 2 volume :=
  (memLp_congr_ae (scalarExhaustionCoordinateCLM_ae f)).mp
    (Lp.memLp (scalarExhaustionCoordinateCLM f))

/-- An actual vector norm cap bounds its scalar coordinate. -/
theorem ae_scalarCoordinate_le_of_normCap (ν : VectorL2) {κ : ℝ}
    (hcap : ν ∈ normCap volume κ) : ∀ᵐ x, ν x 0 ≤ κ := by
  filter_upwards [hcap] with x hx
  exact (le_abs_self (ν x 0)).trans ((PiLp.norm_apply_le (ν x) 0).trans hx)

/-- The exact heat convolution is capped off the actual global scalar active set. -/
theorem heatConvolution_le_cap_off_activeSet (hn : 1 ≤ d)
    (U : ScalarState) (f ν : VectorL2)
    (hu0 : ∀ᵐ x, 0 ≤ globalVectorDirichletObservation U x 0)
    (hpde : ∀ j : Fin 1, ∀ W : H01 (univ : Set X), laplaceBilin univ (U j) W =
      ⟪univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν, W.val 0⟫)
    (hf0 : ∀ᵐ x, 0 ≤ f x 0) {κ : ℝ} (hcap : ν ∈ normCap volume κ)
    {a t : ℝ} (hroot : IsHeatTangencyParameter d a) (ht : 0 < t) :
    ∀ᵐ x, x ∉ globalBalayageActiveSet U →
      heatConvolution t (fun y ↦ f y 0) x ≤ κ * heatBoundFormula d a (rho d * a) := by
  have hρ := rho_pos d hn
  have ha : 0 < a := lt_of_le_of_lt (by positivity) hroot.1.1
  have hcontact := heatKernelMajorant_pairing_nonneg_off_activeSet hn U f ν hu0 hpde hroot ht
  have hbound := ae_kernel_source_pairing_le_cap (heatKernel d t) (heatKernelMajorant d a t)
    (integrable_heatKernel d ht) (Eventually.of_forall fun y ↦ (heatKernel_pos d ht y).le)
    (integrable_heatKernelMajorant d hn ha ht) (heatKernelMajorant_nonneg_ae d hn hroot ht)
    (heatKernel_le_majorant_ae d hn hroot ht) (fun y ↦ f y 0) (fun y ↦ ν y 0)
    (memLp_scalarCoordinate f) (memLp_scalarCoordinate ν) hf0 κ
    (ae_scalarCoordinate_le_of_normCap ν hcap) (fun x ↦ x ∉ globalBalayageActiveSet U)
    (hcontact.mono fun _ hx ↦ hx.2)
  filter_upwards [hbound] with x hx
  intro hzero
  have h := hx hzero
  rw [integral_heatKernelMajorant d hn ha ht] at h
  change (∫ y, heatKernel d t (x - y) * f y 0) ≤ _
  convert h using 1
  apply integral_congr_ae
  filter_upwards with y
  simp only [heatKernel, norm_sub_rev x y]

/-- The exact Poisson convolution is capped off the actual global scalar active set. -/
theorem poissonConvolution_le_cap_off_activeSet (hn : 1 ≤ d)
    (U : ScalarState) (f ν : VectorL2)
    (hu0 : ∀ᵐ x, 0 ≤ globalVectorDirichletObservation U x 0)
    (hpde : ∀ j : Fin 1, ∀ W : H01 (univ : Set X), laplaceBilin univ (U j) W =
      ⟪univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν, W.val 0⟫)
    (hf0 : ∀ᵐ x, 0 ≤ f x 0) {κ : ℝ} (hcap : ν ∈ normCap volume κ)
    {a t : ℝ} (hroot : IsPoissonTangencyParameter d a) (ht : 0 < t) :
    ∀ᵐ x, x ∉ globalBalayageActiveSet U →
      poissonConvolution t (fun y ↦ f y 0) x ≤ κ * poissonBoundFormula d a (rho d * a) := by
  have hρ := rho_pos d hn
  have ha : 0 < a := lt_of_le_of_lt (by positivity) hroot.1.1
  have hcontact :=
    poissonKernelMajorant_pairing_nonneg_off_activeSet hn U f ν hu0 hpde hroot ht
  have hbound :=
    ae_kernel_source_pairing_le_cap (poissonKernel d t) (poissonKernelMajorant d a t)
      (integrable_poissonKernel d ht)
      (Eventually.of_forall fun y ↦ (poissonKernel_pos d ht y).le)
      (integrable_poissonKernelMajorant d hn ha ht)
      (poissonKernelMajorant_nonneg_ae d hn hroot ht)
      (poissonKernel_le_majorant_ae d hn hroot ht) (fun y ↦ f y 0) (fun y ↦ ν y 0)
      (memLp_scalarCoordinate f) (memLp_scalarCoordinate ν) hf0 κ
      (ae_scalarCoordinate_le_of_normCap ν hcap) (fun x ↦ x ∉ globalBalayageActiveSet U)
      (hcontact.mono fun _ hx ↦ hx.2)
  filter_upwards [hbound] with x hx
  intro hzero
  have h := hx hzero
  rw [integral_poissonKernelMajorant d hn ha ht] at h
  change (∫ y, poissonKernel d t (x - y) * f y 0) ≤ _
  convert h using 1
  apply integral_congr_ae
  filter_upwards with y
  simp only [poissonKernel, norm_sub_rev x y]

/-- The exact heat bound is at least one, by genuine kernel domination and mass one. -/
theorem one_le_heatBoundFormula_of_tangency (hn : 1 ≤ d) {a : ℝ}
    (hroot : IsHeatTangencyParameter d a) : 1 ≤ heatBoundFormula d a (rho d * a) := by
  have ht : (0 : ℝ) < 1 := by norm_num
  have hρ := rho_pos d hn
  have ha : 0 < a := lt_of_le_of_lt (by positivity) hroot.1.1
  calc
    1 = ∫ x, heatKernel d 1 x := (integral_heatKernel d ht).symm
    _ ≤ ∫ x, heatKernelMajorant d a 1 x :=
      integral_mono_ae (integrable_heatKernel d ht)
        (integrable_heatKernelMajorant d hn ha ht) (heatKernel_le_majorant_ae d hn hroot ht)
    _ = _ := integral_heatKernelMajorant d hn ha ht

/-- The exact Poisson bound is at least one, by genuine kernel domination and mass one. -/
theorem one_le_poissonBoundFormula_of_tangency (hn : 1 ≤ d) {a : ℝ}
    (hroot : IsPoissonTangencyParameter d a) :
    1 ≤ poissonBoundFormula d a (rho d * a) := by
  have ht : (0 : ℝ) < 1 := by norm_num
  have hρ := rho_pos d hn
  have ha : 0 < a := lt_of_le_of_lt (by positivity) hroot.1.1
  calc
    1 = ∫ x, poissonKernel d 1 x := (integral_poissonKernel d ht).symm
    _ ≤ ∫ x, poissonKernelMajorant d a 1 x :=
      integral_mono_ae (integrable_poissonKernel d ht)
        (integrable_poissonKernelMajorant d hn ha ht)
        (poissonKernel_le_majorant_ae d hn hroot ht)
    _ = _ := integral_poissonKernelMajorant d hn ha ht

/-- A genuine scalar `L²` input injected into the one-coordinate Euclidean output space. -/
def scalarSemigroupVectorInput (f : Lp ℝ 2 (volume : Measure X)) : VectorL2 :=
  (vectorDirichletInjection (m := 1) 0).compLpL 2 volume f

theorem scalarSemigroupVectorInput_ae (f : Lp ℝ 2 (volume : Measure X)) :
    scalarSemigroupVectorInput f =ᵐ[volume] fun x ↦ EuclideanSpace.single 0 (f x) := by
  filter_upwards [(vectorDirichletInjection (m := 1) 0).coeFn_compLpL (p := 2) f]
    with x hx
  exact hx.trans (vectorDirichletInjection_apply 0 (f x))

theorem scalarSemigroupVectorInput_coordinate_ae (f : Lp ℝ 2 (volume : Measure X)) :
    (fun x ↦ scalarSemigroupVectorInput f x 0) =ᵐ[volume] f := by
  filter_upwards [scalarSemigroupVectorInput_ae f] with x hx
  simp only [hx, PiLp.single_apply, ite_eq_left]

/-- Nonnegative integrable actual scalar `L²` input has one genuine active set that controls
both exact semigroup convolutions at every positive time with the article's exact masses. -/
theorem exists_scalarSemigroup_off_active_caps {n : ℕ}
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (hf : Integrable (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ))
    (hf0 : ∀ᵐ x, 0 ≤ f x) (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin (n + 1)))) 1,
      ENNReal.ofReal (κ : ℝ) * volume (globalBalayageActiveSet U) ≤ ∫⁻ x, ‖f x‖ₑ ∧
      (∀ a : ℝ, IsHeatTangencyParameter (n + 1) a → ∀ t : ℝ, 0 < t →
        ∀ᵐ x, x ∉ globalBalayageActiveSet U →
          heatConvolution t f x ≤ (κ : ℝ) * heatBoundFormula (n + 1) a (rho (n + 1) * a)) ∧
      (∀ a : ℝ, IsPoissonTangencyParameter (n + 1) a → ∀ t : ℝ, 0 < t →
        ∀ᵐ x, x ∉ globalBalayageActiveSet U →
          poissonConvolution t f x ≤
            (κ : ℝ) * poissonBoundFormula (n + 1) a (rho (n + 1) * a)) := by
  let F := scalarSemigroupVectorInput f
  have hF : Integrable (F : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin 1)) := by
    apply ((vectorDirichletInjection (m := 1) 0).integrable_comp hf).congr
    filter_upwards [scalarSemigroupVectorInput_ae f] with x hx
    exact (vectorDirichletInjection_apply 0 (f x)).trans hx.symm
  have hF0 : ∀ᵐ x, 0 ≤ F x 0 := by
    filter_upwards [hf0, scalarSemigroupVectorInput_coordinate_ae f] with x hx heq
    rwa [heq]
  obtain ⟨ν, U, _, hu0, hcap, hν, _, _, _, hpde, halign, _⟩ :=
    exists_wholeSpace_scalarPositiveBalayage F hF hF0 κ hκ
  have hκreal : 0 < (κ : ℝ) := by exact_mod_cast hκ
  have hmass := cap_measure_globalBalayageActiveSet U F ν hκreal hF hν hpde halign
  have hmass_eq : (∫⁻ x, ‖F x‖ₑ) = ∫⁻ x, ‖f x‖ₑ := by
    apply lintegral_congr_ae
    filter_upwards [scalarSemigroupVectorInput_ae f] with x hx
    change ‖scalarSemigroupVectorInput f x‖ₑ = ‖f x‖ₑ
    rw [hx]
    simp only [enorm_eq_nnnorm, PiLp.nnnorm_single]
  rw [hmass_eq] at hmass
  refine ⟨U, hmass, ?_, ?_⟩
  · intro a ha t ht
    have hbound := heatConvolution_le_cap_off_activeSet (by omega) U F ν hu0 hpde hF0 hcap ha ht
    filter_upwards [hbound] with x hx
    intro hzero
    have h := hx hzero
    convert h using 1
    apply integral_congr_ae
    filter_upwards [scalarSemigroupVectorInput_coordinate_ae f] with y hy
    rw [hy]
  · intro a ha t ht
    have hbound :=
      poissonConvolution_le_cap_off_activeSet (by omega) U F ν hu0 hpde hF0 hcap ha ht
    filter_upwards [hbound] with x hx
    intro hzero
    have h := hx hzero
    convert h using 1
    apply integral_congr_ae
    filter_upwards [scalarSemigroupVectorInput_coordinate_ae f] with y hy
    rw [hy]

end PartialBalayage
