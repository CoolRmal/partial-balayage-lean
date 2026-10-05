/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.TableDefinitions
public import PartialBalayage.Maximal.HeatMajorant
public import PartialBalayage.Maximal.PoissonMajorant

/-!
# The actual unique semigroup tangency parameters

The selected real numbers satisfy the exact algebraic tangency equations in the
article's intervals in every positive dimension. Existence and uniqueness are proved;
the parameter definitions have no analytical-certificate or input-function argument.
-/

@[expose] public section

noncomputable section

open PartialBalayage.Constants

namespace PartialBalayage

theorem isHeatTangencyParameter_selected (n : ℕ) (hn : 1 ≤ n) :
    IsHeatTangencyParameter n (heatTangencyParameter n) :=
  Classical.epsilon_spec (existsUnique_isHeatTangencyParameter n hn).exists

theorem isPoissonTangencyParameter_selected (n : ℕ) (hn : 1 ≤ n) :
    IsPoissonTangencyParameter n (poissonTangencyParameter n) :=
  Classical.epsilon_spec (existsUnique_isPoissonTangencyParameter n hn).exists

theorem heatTangencyParameter_pos (n : ℕ) (hn : 1 ≤ n) : 0 < heatTangencyParameter n := by
  have h := (isHeatTangencyParameter_selected n hn).1.1
  exact lt_of_le_of_lt (by positivity [rho_pos n hn]) h

theorem poissonTangencyParameter_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < poissonTangencyParameter n := by
  have h := (isPoissonTangencyParameter_selected n hn).1.1
  exact lt_of_le_of_lt (by positivity [rho_pos n hn]) h

end PartialBalayage
