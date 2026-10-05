/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Rat.Lemmas

/-!
# Normalized rational literals for exact certificates

The denominator and coprimality proofs are checked once at declaration time.
Reading the resulting rational avoids recomputing normalization at each use.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- An already reduced rational, with ordinary kernel checked proof arguments. -/
def exactRationalLiteral (n : ℤ) (d : ℕ)
    (hd : d ≠ 0 := by decide +kernel)
    (hc : n.natAbs.Coprime d := by decide +kernel) : ℚ :=
  Rat.mk' n d hd hc

/-- The directly constructed rational is exactly the usual quotient. -/
theorem exactRationalLiteral_eq (n : ℤ) (d : ℕ) (hd : d ≠ 0)
    (hc : n.natAbs.Coprime d) : exactRationalLiteral n d hd hc = (n : ℚ) / d := by
  exact (Rat.mk_eq_mkRat n d hd hc).trans (Rat.mkRat_eq_div n d)

end PartialBalayage.Maximal.Square
