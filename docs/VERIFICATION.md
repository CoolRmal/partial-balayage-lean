# Verification evidence

## Current scope

The repository now includes fifteen article rows. The planar centred-square target
below $$3.616$$, its large numerical certificate development, and its specialized
validation workflows have been removed from the current scope. The complete
sixteen-row article table remains visible in the [README](../README.md), with that
row explicitly excluded. The separate
[centered-maximal-constant](https://github.com/CoolRmal/centered-maximal-constant)
repository formalizes the weaker square bound $$c(M_\square)\le3.879$$.

Fresh ordinary CI and protected official full verification are pending for the
cleaned fifteen-row snapshot. No current complete verification or Palomar
registration is claimed. The history below refers to immutable earlier commits.

## Accepted earlier fifteen-row snapshot

The corrected fifteen-row source
`e301f763ae0c819976384ea733f7327e80ce1c44` passed
[official full preflight 37404883784](https://github.com/CoolRmal/partial-balayage-lean/actions/runs/37404883784)
with zero errors and warnings. Comparator matched the Challenge and Solution
statements, and Lean, NanoDa, and con-ron accepted the solution using only the
permitted standard axioms.

That scope included the full complex-input Riesz vector; Beurling; full and
traceless Frobenius Hessians; both projections; centred intervals and Euclidean
balls; and the six exact Poisson and heat bounds. It excluded the strict planar
square row. Earlier snapshots with a real-only Riesz input do not establish the
complete article Riesz statement; the cited corrected snapshot is the relevant
historical acceptance.

## Unsuccessful sixteen-row attempts

The later source `0055cdf5b947f4e23b0b736a297ab38b48b1a270` added the square
statement. Its
[official full attempt 37447417954](https://github.com/CoolRmal/partial-balayage-lean/actions/runs/37447417954)
was a failure. The cold Solution build returned zero after 16,581.368 seconds
(4,739 jobs), and Solution export returned zero after 72.256 seconds. The
Comparator supervisor exhausted the remaining time budget without a completed
Comparator verdict. The report did not establish an inner independent-kernel
bottleneck or complete sixteen-row acceptance.

[Ordinary CI 37447273104](https://github.com/CoolRmal/partial-balayage-lean/actions/runs/37447273104)
completed its Lean build (4,742 jobs), but its Comparator and documentation jobs
were cancelled at their 350-minute limits. A source build is not a Comparator
pass. Neither run constitutes Palomar registration.

The large exact arithmetic certificates made complete verification of the square
row difficult within the fixed budget. Local and Linux certificate experiments
were diagnostic evidence only. They did not establish full sixteen-row acceptance.
The square proof has now been removed from scope rather than advertised as a
verified article result. Detailed historical logs and earlier source remain in
Git history and the linked runs.

## Required verification of the cleaned snapshot

1. Ordinary CI must pass its build, source and metadata checks, documentation, and
   Comparator jobs for the exact cleaned public commit.
2. The unchanged protected official workflow must run in full mode on that commit
   and `comparator.json`, with the approved profile and all independent kernels.
3. Its mechanical report must be an actual pass and bind the intended repository,
   source commit, Comparator path, fifteen targets, and permitted axioms.
4. Intake and subsequent registration require the human maintainer's agreement and
   consent to the exact delivered review.

A cache, standalone build, imported axiom audit, or selected-kernel experiment does
not replace these gates. See [PALOMAR.md](PALOMAR.md) for the procedure.
