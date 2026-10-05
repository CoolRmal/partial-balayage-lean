/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage

/-!
# Implementations of the currently advertised statements

Comparator checks this module independently against `Challenge.lean`.
No unproved row of the article is represented by a conditional substitute here.
-/

@[expose] public section

open scoped ENNReal

namespace PartialBalayage

/-- The centred interval weak type `(1,1)` constant is at most `2`. -/
theorem interval_weakTypeConstant_le_two : cubeWeakTypeConstant 1 ≤ 2 :=
  Maximal.interval_weakTypeConstant_le_two

/-- The centred planar Euclidean-ball weak type constant is at most `e`. -/
theorem ball_weakTypeConstant_two_le_exp :
    ballWeakTypeConstant 2 ≤ ENNReal.ofReal (Real.exp 1) :=
  Maximal.ball_weakTypeConstant_two_le_exp

/-- The centred Euclidean-ball weak type bound in dimensions `n ≥ 3`. -/
theorem ball_weakTypeConstant_le_rpow (n : ℕ) (hn : 3 ≤ n) :
    ballWeakTypeConstant n ≤
      ENNReal.ofReal (((n : ℝ) / 2) ^ ((n : ℝ) / ((n : ℝ) - 2))) :=
  Maximal.ball_weakTypeConstant_le_rpow n hn

end PartialBalayage
