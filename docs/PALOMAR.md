# Palomar preparation and registration

Registration is pending. The current submission scope is fifteen rows of
[Two partial balayage principles](https://coolrmal.github.io/articles/two-partial-balayage-principles/).
The planar square bound below $$3.616$$ is excluded. The complete article table
and this distinction are visible in the [README](../README.md).
The cleaned public snapshot requires fresh verification before intake.

The authoritative sources are the live
[submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
[protocol](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/docs/specification.md),
and [agent instructions](https://submit.palomar-registry.org/llms.txt).
Read them again before using intake; this document is a project checklist.

## Repository checks

- Retain the pinned `lean-toolchain`, Lakefile, `lake-manifest.json`,
  `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`, and
  the matching Apache-2.0 licence.
- Challenge must expose the fifteen actual mathematical statements and their
  hypotheses, using only allowed independent dependencies. The excluded square
  row must not remain as a placeholder or conditional substitute.
- Solution must prove the matching statements. Deliberate Challenge holes must
  not enter those proofs. Permit only `propext`, `Classical.choice`, and
  `Quot.sound`, including legitimate subsets; reject `sorryAx`, native reduction,
  and custom axioms.
- Preserve human author headers, dependency provenance, exact formulas, the full
  intended operator norms and input domains, and honest AI-use disclosure.
- Keep scope consistent across the README, metadata, Challenge, Solution, and
  Comparator. Historical verification is evidence about its exact earlier
  snapshot, not acceptance of the cleaned source.

## Checks for the exact public commit

Run ordinary CI, then dispatch the protected official full preflight:

```bash
gh workflow run palomar-preflight.yml --repo OWNER/REPOSITORY --ref main \
  -f commit=FULL_40_CHARACTER_COMMIT
```

The committed workflow pins PalomarSubmission to
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, selects full mode, and uses
`palomar-standard-v1` for the approved GitHub-hosted profile. Its fixed budget
and protected kernel configuration must remain unchanged. Source and cache
optimizations do not justify relaxing the official verification requirements.

Inspect the actual mechanical report and logs. Require a completed pass binding
this repository, the exact source commit, `comparator.json`, all fifteen targets,
permitted axioms, and the actual protected kernel results. A local build or
selected independent-kernel pass does not replace full preflight. The workflow
itself does not submit or register the project.

## Intake and registration

Use the final verified public commit and `comparator.json` at
[submit.palomar-registry.org](https://submit.palomar-registry.org/).
Repository write access alone does not establish human authorship.

1. Show the human the repository, exact commit, Comparator path, and claimed
   maintainer relationship. Obtain their agreement before intake.
2. Follow the current documented HTTPS/`gh` proof route and returned challenge
   instructions within its fifteen-minute lifetime. Keep pending secrets and
   bearer tokens in private files, outside Git and public output.
3. Preserve owned temporary proof artifacts on unknown or unconsumed verification
   outcomes. Clean up only the owned artifacts when the service has confirmed a
   successful answer or known consumption; do not blindly retry a mutation.
4. Inspect the actual submission and delivered review under the protocol's polling
   limits. An unregistered review remains private. Correct blocking issues and
   reverify the exact new commit when required.
5. Show the human the complete review and its exact digest. Registration publishes
   the record, source, redacted review, and preservation tags, so obtain a second
   agreement to that exact review before registering.
6. Confirm the actual registered state and public entry. Successful verification
   or review alone is not registration.

No intake or registration is claimed for this cleanup. The historical accepted
fifteen-row snapshot and failed sixteen-row attempts are summarized in
[VERIFICATION.md](VERIFICATION.md).
