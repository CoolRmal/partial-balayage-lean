# Formalization instructions

Current scope, as directed by the human author: fifteen comparator statements from the
published article's abstract table, excluding the strict planar square bound below 3.616 and
its proof. The README documents the complete article table and clearly distinguishes the
excluded square result. Retain `cubeWeakTypeConstant 1` and its centred-interval theorem;
the exclusion concerns the planar square result. Do not advertise the excluded result as
formalized, replace an operator with an arbitrary abstraction, add an assumption equivalent
to a desired bound, or substitute rounded approximations for exact constants. Preserve the
exact domains, dimension assumptions and constants of all fifteen submitted statements.

Use $$ for LaTeX in Markdown. Preserve copied authorship headers. Every Lean source uses
`module`. Challenge imports only allowed libraries and states each advertised result
independently. Solutions use only `propext`, `Classical.choice` and `Quot.sound`: no missing
proofs, custom axioms or `native_decide`.

Push validated milestones to the public origin regularly. Submission requires all fifteen
current targets and a passing full Palomar preflight for the exact revised public commit;
earlier snapshots' checks do not establish this revision's acceptance. Preserve the protected
verification profile and full kernel coverage. Keep metadata, comparator and README scope
consistent, retain human authorship and disclose AI assistance. Obtain the required human
submission consent for the concrete repository, commit and configuration. Register only
after inspecting the actual nonblocking review and obtaining the separate required human
consent to publication of that exact review and verified snapshot.
