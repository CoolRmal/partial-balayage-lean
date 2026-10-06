# Formalization instructions

Final scope: every upper-bound row of the published article's abstract table. Do not silently
reduce scope, replace an operator with an arbitrary abstraction, add an assumption equivalent
to the desired bound, or substitute rounded approximations for exact constants. The current
sixteen-row comparator covers the full table. Keep all operator domains and strict bounds exact.

Use $$ for LaTeX in Markdown. Preserve copied authorship headers. Every Lean source uses
`module`. Challenge imports only allowed libraries and states each advertised result
independently. Solutions use only `propext`, `Classical.choice` and `Quot.sound`: no missing
proofs, custom axioms or `native_decide`.

Push validated milestones to the public origin regularly. Final registration requires every
target row, passing comparator and full Palomar preflight for the exact submitted commit,
accurate metadata and inspection of the returned review. Register only the exact complete and verified public snapshot, after the required human consent.
