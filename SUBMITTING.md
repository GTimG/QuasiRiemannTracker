# Submitting a result

1. Start from the current `main` branch. Add Lean source under
   `submissions/YYYY-MM-DD-<slug>/src/Candidate/`, with theorem
   `Candidate.bound` in `Main.lean`. Use the pinned dependencies in
   [verifier/pins.json](verifier/pins.json) and
   [verifier/standard/lake-manifest.json](verifier/standard/lake-manifest.json).

   Use the original PR creation date in UTC as the directory prefix. The date
   appears only once: choose a lowercase slug without another date, such as
   `example-bound`. Admission checks the prefix against the PR creation time.
   Keep that original directory name when updating the proof on later days.

   For an imported historical result, use its documented original source
   date instead of the new PR date, for example
   `submissions/2026-10-08-example-bound/` for an October 8 source imported in
   a later PR. The earlier directory date automatically labels the PR as
   Historical; no explicit historical flag or date field is needed.

   The directory date must be a real `YYYY-MM-DD` date and cannot be later
   than the PR creation date. Include the original source and date evidence
   in the description and references. Historical imports follow the same
   proof and license requirements as other submissions.

2. **Commit `submissions/YYYY-MM-DD-<slug>/metadata.json` alongside the Lean source.**
   Admission reads this required file from the exact PR head. The submission
   directory contains:

   ```text
   submissions/2026-10-27-example-bound/
     metadata.json
     src/Candidate/Main.lean
     src/Candidate/...           supporting Lean modules
   ```

   Use this JSON structure for a submission that imports the OpenAI baseline:

   ```json
   {
     "title": "Result title",
     "authors": [{ "name": "Your name" }],
     "description": "Method and attribution to previous work.",
     "dependencies": ["openai-baseline"],
     "agent_traces": []
   }
   ```

   Required fields are `title`, `authors` (a nonempty array of objects with
   `name` and an optional HTTPS `url`), and `description`. The description
   explains the method and credits previous work.

   Declare each directly imported submission in `dependencies`, using its
   stable result ID, without the new directory date prefix. It defaults to an
   empty list.
   `builds_on` records attribution to existing result IDs; `dependencies`
   supplies the source modules available to imports.

   Use `published_at` for a documented public announcement timestamp, such as
   `2026-10-08T18:48:49Z`, and cite its evidence in `references`. This applies
   equally to new and imported results; it makes no verification claim.

   The other supported fields are `license` and `references` (an array of
   objects with `label` and HTTPS `url`), and `agent_traces` (an optional array
   of embedded JSON exports). Agent traces are recommended: prefer
   [ATIF (Agent Trajectory Interchange Format)](https://docs.harborframework.com/agents/atif);
   native JSON objects or arrays are also accepted. Omit `agent_traces` or leave
   it empty if no trace is available. Embedded traces may total up to 1 MiB;
   the complete metadata file may be up to 2 MiB. The
   [metadata validator](verifier/submission-metadata.mjs) defines the field
   formats and size limits.

   Remove credentials and private information before committing traces. Install
   [Gitleaks v8.30.1](https://github.com/gitleaks/gitleaks/releases/tag/v8.30.1)
   on your `PATH`, then check locally before pushing:

   ```sh
   node scripts/check-agent-traces.mjs submissions/YYYY-MM-DD-example-bound/metadata.json
   ```

   Omit the path to check all submission metadata. Supplied traces must pass the
   automatic secret check, which scans raw content and decoded JSON strings and
   redacts findings in logs. This is a basic safeguard; CI runs after upload.
   Revoke any real credential accidentally pushed.

3. Open a PR using the [submission template](.github/PULL_REQUEST_TEMPLATE.md).
   Start its body with the result ID, exact bound, and decimal approximation.
   For a new submission, the result ID is the slug without the date prefix:

   ```text
   QRH-Result: example-bound
   QRH-Bound: 7/8
   QRH-Decimal: 0.875
   ```

   `QRH-Bound` is a reduced fraction; it is the value that is ranked. Give an
   accurate truncated `QRH-Decimal` of it, with at most 200 fractional digits.
   A bound below the current best verified bound must be lower within those
   digits; equal or larger bounds accept any precision. These PR fields declare
   the bound; the committed `metadata.json` supplies its publication metadata.

   Exact algebraic bounds are encouraged when they are the natural statement.
   Add `QRH-Exact` with the expression, and keep a rational `QRH-Bound` above
   it, close enough to rank as intended:

   ```text
   QRH-Result: example-exact
   QRH-Exact: (777 − √1081) / 852
   QRH-Bound: 7/8
   QRH-Decimal: 0.875
   ```

   Expressions use integers, `+`, `−`, `*`, `/`, and `√`. `√` applies to a
   positive integer and `/` divides by a positive integer; `k√n` means
   $k \cdot \sqrt{n}$. Write the expression canonically; the check reports
   the canonical spelling. `Candidate/Main.lean` then proves both theorems,
   stated with `Real.sqrt`:

   ```lean
   theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
       (hs : ((777 - Real.sqrt 1081) / 852 : ℝ) < s.re)
       (hpole : ¬ (χ = 1 ∧ s = 1)) : DirichletCharacter.LFunction χ s ≠ 0
   theorem bound_le : ((777 - Real.sqrt 1081) / 852 : ℝ) ≤ (7 / 8 : ℝ)
   ```

   Existing submissions retain their stable result IDs and Lean namespaces when
   their folders are renamed, even if an older ID includes a date. Use those
   unchanged IDs in `QRH-Result` and dependency declarations.

   For algebraic numbers beyond square-root expressions, use
   `QRH-Exact: root([c0,c1,...,cn],lower,upper)`. The integer coefficients
   are in ascending order: `c0 + c1*x + ... + cn*x^n`. The polynomial
   must be primitive (coefficient gcd 1), with positive leading coefficient,
   degree 2 through 32. The endpoints are reduced signed fractions with
   positive denominators and `lower < upper`. The expression has the same
   256-character limit as other exact expressions. For example,
   `root([-2,0,1],1/1,2/1)` specifies the positive square root of 2.

   This declaration adds a third checked theorem, `Candidate.bound_isolated`,
   proving that exactly one root lies in the open interval. The exact threshold
   is the infimum of that singleton root set. For the example above, the
   generated Lean expression is
   `sInf {x | (1 / 1) < x ∧ x < (2 / 1) ∧ ((-2) + x * (0 + x * 1)) = 0}`.
   Use this literal Horner expression in `bound` and `bound_le`, and prove
   `bound_isolated : ∃! x : ℝ, (1 / 1) < x ∧ x < (2 / 1) ∧
   ((-2) + x * (0 + x * 1)) = 0`.
   All three statements are checked by Lean, NanoDa and con-ron. Parsing does
   not certify a root's existence or uniqueness; these remain proof obligations.
   Ranking continues to use the rational `QRH-Bound`.

4. GitHub Actions checks the exact PR head, including drafts. Comparator checks
   the statement and allowed axioms against the
   [canonical target](verifier/upstream-challenge.lean), with the submitted bound
   substituted for $7/8$, and for an exact bound also `bound_le`. Lean, NanoDa,
   and con-ron must all accept the proof.
   After review and merge, the website adds the result automatically.

Reusable modules live in `src/Submissions/<result_id>/`, with hyphens in the
result ID replaced by underscores. Declare direct source dependencies in
`metadata.json`, for example `"dependencies": ["openai-baseline"]`, then import:

```lean
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Nonvanishing
```

The baseline contains the relevant OpenAI proof sources at the revision recorded
in [NOTICE](NOTICE). Every submission can use them through this dependency.
`Submissions.openai_baseline.Main` also exposes its bound theorem. A dependency
and its transitive imports are built from the same PR commit. Changes to shared
source or dependency declarations trigger checks for all dependent results.
Independent modules compile concurrently within the worker's CPU and memory limits.

Verified bounds of any strength are eligible for admission. Improving bounds
advance the best verified bound shown on the site. Maintenance PRs use a plain
description; edits to proofs and bounds trigger their respective validations.

See [HOSTING.md](HOSTING.md) for how submission data becomes the website.
