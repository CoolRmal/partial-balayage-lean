# Palomar preparation and registration

Registration is pending. This project targets all bounds in the table of
[Two partial balayage principles](https://coolrmal.github.io/articles/two-partial-balayage-principles/).
Do not describe the table as fully formalized, submit it as complete, or claim a
Palomar registration until every advertised bound has a proof and the checks
below have passed for the same public commit.

The user has authorized creating the public repository, pushing its development,
and preparing its submission. Submission must accurately identify the human
responsible author or maintainer; repository write access alone is not authorship.

## Repository requirements

These requirements were checked against Palomar's live policy on 2026-10-05.
The [submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
and [protocol](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/docs/specification.md)
are authoritative; read the live
[agent instructions](https://submit.palomar-registry.org/llms.txt) before intake.

- Keep `lean-toolchain`, one Lakefile, the committed `lake-manifest.json`,
  `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`, and
  exactly one root licence file. The licence must match `project.license`.
- Use Lean at least `leanprover/lean4:v4.35.0-rc2`, exactly matching the resolved
  canonical Mathlib revision's toolchain. Pin all Git dependencies to public,
  credential-free GitHub URLs and full lowercase 40-character commits.
- Every submitted regular `.lean` file must use `module` and have at most 10,000
  physical lines. `lakefile.lean` is exempt only from the header. Exclude `.git`
  and `.lake`; do not submit Lean symlinks or compiled artifacts.
- Keep Challenge at most 1,000 lines and 100 KiB, preferably at most 300 lines
  and 32 KiB. Its transitive imports may use only Lean core, canonical Mathlib,
  Tau Ceti, or CSLib. Definitions must have their ordinary mathematical meaning
  and precise docstrings; expose every principal claim and material hypothesis.
- Comparator may permit only `propext`, `Quot.sound`, and `Classical.choice`.
  Deliberate Challenge holes are allowed; Solution proofs must not depend on
  `sorryAx`, `Lean.ofReduceBool`, or custom axioms. Do not put `external_kernels`
  in the submitted configuration. Palomar ignores `enable_nanoda` and supplies
  its protected independent-kernel configuration.
- Use `formalization.yaml` v0.4 with human authors and responsible maintainers,
  precise scope, a factual abstract, subject classification, source provenance,
  honest AI-use disclosure, and the review actually completed. This is a
  source-based formalization of the linked article, not an `original-proof`.
  The article can use source type `web discussion` and relationship `formalizes`.

## Checks for the exact commit

The template CI checks source requirements, builds, metadata/licence, API
documentation, and Comparator on Linux. The bundled `lake comparator` uses
bubblewrap; a macOS development build is not a sandboxed Comparator check.
Run the project's ordinary CI first, then dispatch the official full preflight:

```bash
gh workflow run palomar-preflight.yml --repo OWNER/REPOSITORY --ref main \
  -f commit=FULL_40_CHARACTER_COMMIT
gh run list --repo OWNER/REPOSITORY --workflow palomar-preflight.yml
gh run download RUN_ID --repo OWNER/REPOSITORY \
  --pattern 'mechanical-report-*' --dir REPORT_DIRECTORY
```

The workflow pins PalomarSubmission to
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` in both its `uses` reference and
`pipeline_commit`. It selects `mode: full` and
`execution_profile: palomar-standard-v1` for ordinary GitHub-hosted runners.
Inspect the downloaded `mechanical-report.json`: require `status: pass` and
confirm the repository, source commit, project path, and Comparator path match
the intended submission. A local build or standalone Comparator pass does not
replace this full preflight. The workflow is manual and does not submit anything.

## Submission and registration

The sole intake is [submit.palomar-registry.org](https://submit.palomar-registry.org/).
Use the final public 40-character commit and `comparator.json`. For an agent,
the documented HTTPS route proves push access through authenticated `gh`:

1. `POST /api/submit` with repository, commit, Comparator path, and the agreed
   human authorization relationship. An ordinary responsible-maintainer claim
   uses `authorization_relationship: "maintainer"`.
2. Create the returned challenge tag at that commit and a new secret gist
   containing the same challenge, following the returned instructions.
3. `POST /api/verify` with the pending secret and gist identifier. Store its
   bearer access token privately; never commit or print it. Delete the temporary
   tag and gist after verification answers. Complete this proof within the
   fifteen-minute intake lifetime. Do not automate browser sign-in.
4. Read `GET /api/submission` using the bearer header, at most once a minute
   during verification and once every five minutes while awaiting review.
   Read `GET /api/review` when available. Keep an unregistered review private.
5. If the review requests correctable changes, commit and push the corrections,
   rerun the checks, and submit the new exact commit.
6. Registration requires a review with no blocking problems and consent to that
   exact review. Show the human the review and explain that registration publishes
   the record, source, redacted review, and immutable preservation tags. After
   they approve that review, `POST /register` with its `review_sha256`, then
   confirm `registered` and the public entry. A successful verification or
   review is not itself registration.

Keep access tokens and pending secrets out of Git, public logs, issues, and pull
requests. If the proof route cannot establish the required tag and secret gist,
the user must complete Palomar's browser flow themselves.
