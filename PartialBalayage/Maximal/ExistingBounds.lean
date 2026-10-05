/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Definitions
public import CenteredMaximal.UpperBound
public import CenteredMaximal.Ball.AEChallengeReduction
public import CenteredMaximal.Ball.BallGreenCertificates

/-!
# Bounds for intervals and Euclidean balls

The interval bound follows from the centred Vitali covering argument. The planar and
higher-dimensional ball bounds follow from the logarithmic and Newtonian obstacle certificates.
The imported proof files retain the authorship and license of the original development.
-/

@[expose] public section

open scoped ENNReal

namespace PartialBalayage.Maximal

/-- The centred maximal operator over intervals has weak type constant at most two. -/
theorem interval_weakTypeConstant_le_two : cubeWeakTypeConstant 1 ≤ 2 := by
  simpa [cubeWeakTypeConstant, IsCubeWeakTypeBound, cubeMaximalFunction,
    CenteredMaximal.weakTypeConstant, CenteredMaximal.IsWeakTypeBound,
    CenteredMaximal.maximalFunction] using
    CenteredMaximal.weakTypeConstant_le (CenteredMaximal.isWeakTypeBound_two_pow 1)

/-- The centred maximal operator over planar Euclidean discs has weak type constant at most
`exp 1`. -/
theorem ball_weakTypeConstant_two_le_exp :
    ballWeakTypeConstant 2 ≤ ENNReal.ofReal (Real.exp 1) := by
  exact CenteredMaximal.Ball.ballWeakTypeConstant_two_le_exp_of_ae_direct_certificates
    CenteredMaximal.Ball.hasRealAEDirectObstacleCertificates_planarKernel.toENNReal

/-- In dimension at least three, the centred Euclidean ball weak type constant is at most
`(n / 2) ^ (n / (n - 2))`. -/
theorem ball_weakTypeConstant_le_rpow (n : ℕ) (hn : 3 ≤ n) :
    ballWeakTypeConstant n ≤
      ENNReal.ofReal (((n : ℝ) / 2) ^ ((n : ℝ) / ((n : ℝ) - 2))) := by
  exact CenteredMaximal.Ball.ballWeakTypeConstant_le_rpow_of_ae_direct_certificates n hn
    (CenteredMaximal.Ball.hasRealAEDirectObstacleCertificates_newtonianKernel n hn).toENNReal

end PartialBalayage.Maximal
