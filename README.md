# Quasi-Riemann Tracker

Live: [gtimg.github.io/QuasiRiemannTracker](https://gtimg.github.io/QuasiRiemannTracker/)

Quasi-Riemann Tracker follows bounds on the real parts of zeros of Dirichlet
L-functions. The timeline and leaderboard show exact bounds, authors, sources,
and verification status. Smaller bounds are stronger; the generalized Riemann
hypothesis corresponds to a bound of $1/2$.

Every result on the website is verified. Verification runs through the project’s
GitHub Actions CI. If CI resources run out, maintainers may run the same
verification checks on maintainer infrastructure.

## Run locally

Use Node.js 22.17 or later. Repository checks also require Python 3.

```sh
npm ci
npm run dev
```

The site runs at `http://127.0.0.1:4173`. `npm run build` creates the static site
in `dist/`; `npm run preview` serves that build. Run `npm run check` to run the
tests and production build.

## Data

Each `submissions/YYYY-MM-DD-<slug>/` directory contains `metadata.json` and its Lean
source in `src/`. Catalogue builds use the current checkout and, when available,
the current tree of the local `admission-records` branch. No commit history,
GitHub API requests, credentials or ignored cache are needed. The
canonical `Candidate.bound` statement supplies the exact bound for modern
submissions, together with `Candidate.bound_le` for an exact algebraic bound;
older entries retain their recorded bounds and revisions.
Builds include submissions present in the checkout. Deployment runs from main,
where merging a submission means it has passed verification through CI or,
when CI resources run out, a maintainer run. Catalogue generation does not repeat
that admission check.

Generated catalogue JSON and `public/certificates/` are ignored by Git. Existing
verification dates and reports come from submission metadata or the existing
`admission-records` branch. These are publication facts, not inclusion checks;
submissions without a record still appear. There is no new publication registry.
Merged submissions retain the existing verification label and link to their
committed Lean source. Dates are displayed only where recorded.

A shallow clone is sufficient. To include the recorded publication dates and
reports, clone the branch tips with `git clone --depth=1 --no-single-branch URL`,
or fetch just the archive tip into an existing shallow clone:

```sh
git fetch --no-tags --depth=1 origin +refs/heads/admission-records:refs/remotes/origin/admission-records
```

Catalogue generation itself never fetches. A main-only shallow clone also
includes every submission and its recorded announcement date, including its precision.

Every catalogue entry has a public announcement date. Checked-in submissions
record it in `published_at`, with a source citation in `references`. For a new
submission without an earlier documented announcement, opening its public PR is
the announcement. Preview checkouts without either timestamp use the directory
date with day-only precision. A calendar day or year is never displayed as an
observed midnight timestamp. PR submission and verification timestamps remain
separate provenance. Imported results use
the same presentation and verification status as other submissions. An earlier
directory date adds the Historical label to the PR only.

The optional `published_at` metadata field records a public announcement as an
ISO 8601 UTC timestamp, with a supporting source link in `references`. Commit
history can establish when the result entered the source history; its timestamp
does not establish when it was first pushed publicly or mathematical priority.
Catalogue generation reads the recorded timestamp from the current checkout;
it never queries upstream history or GitHub. Recorded verification dates and
reports remain fixed.

## Submit

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
   accurate truncated `QRH-Decimal` of it with enough digits to differ from the
   current best verified bound.
   Equal bounds accept any supported decimal precision. These PR fields declare
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

## Hosting

GitHub Actions builds and deploys `main` to GitHub Pages. For another static
host, run `npm run build` and publish `dist/`. Set `QRH_BASE_PATH` to the site's
URL prefix when hosting under a subdirectory.

## License

Project code is licensed under [Apache-2.0](LICENSE). Third-party proofs and
dependencies retain their original licenses and attribution; see [NOTICE](NOTICE).

Workers automatically reuse server-built submission modules from the signed
`submission-build-cache-v1` release. Cache keys bind each module to its Lean source,
imported submission modules, compiler and library contents. Changed modules and
their importers compile again. A proof replay still runs Comparator and all three
kernels. An unavailable or incompatible cache triggers a source build.

### Reuse a maintainer verification receipt

When CI resources run out, maintainers may complete the same verification checks
on maintainer infrastructure. A maintainer can approve the resulting receipt for
reuse in PR admission. The protected workflow first reconstructs the exact
PR source and dependency contract from immutable Git objects. It then validates
the protected registration and full receipt before restoring caches, provisioning
Lean or executing candidate code. The publishing job independently repeats the
receipt validation, checks the current PR and publication metadata, and writes a
durable admission record before granting the required `qrh/pr-admission` check.
The original receipt URL and first successful verification time are preserved.

Authentication comes from maintainer-reviewed evidence and registration in
protected `main`; a hash or a candidate-written `PASS` alone is not authentication.
For an ETH run, retrieve the outside-sandbox evidence over authenticated SSH and
review its source binding, pinned tools/libraries, baseline and adversarial
controls, isolation checks and Comparator/Lean/NanoDa/con-ron acceptance first.
Keep the raw receipt unchanged in `verifier/standard/receipts/<run>/result.json`,
with its hash-bound `contract.json`, `controls.json` and `dependency-pins.json`.
The registration's `report_url` must identify an immutable commit and this evidence
path in this repository. Candidate PRs cannot edit the verifier or register results.

An eligible entry in `verifier/local-results.json` also needs a maintainer-approved
`reuse` object with `schema_version: 1`, `policy_sha256` and `runtime_sha256`.
Compute those hashes with `receiptPolicy(root)` and `receiptRuntime(report)` from
`verifier/receipt-reuse.mjs`, **only after reviewing compatibility**. The policy
hash covers verifier code, challenge, pins, admission workflow and package lock;
the runtime hash binds actual checker/driver binaries and the verified library
inventory. Explicitly review and document any runtime deviation, such as a newer
NanoDa tested against the baseline. Never regenerate approvals merely to clear a
failed check. Tool/dependency or verifier-policy changes require renewed review.

Run `node --test tests/receipt-reuse.test.mjs tests/actions-finalize.test.mjs`
and `npm run check` before publishing an approval or workflow change. Trigger
**PR admission → Run workflow**, select `main`, and supply the PR number. A
successful reuse logs that no replay was needed; it still requires successful
source preparation, receipt validation, ordinary project tests and admission.
Missing approvals use the full isolated verifier. Malformed, stale or incompatible
approved receipts fail closed. A mathematical rejection cannot be overridden by
the infrastructure-failure fallback. Keep branch protection requiring `test` and
`qrh/pr-admission`, with verifier and registration updates reviewed by maintainers.

The server publisher runs from a protected checkout after an isolated build has
passed verification. Run `verifier/actions/setup.py` to prepare the server's
checking environment with the same Lake build products as GitHub workers.
Cache restoration reports compatibility differences in the job log and
`build-cache-status.json` artifact. Copy its `candidate-lib/`, `contract.json`, `result.json`,
profile and prepared `libraries.json` to the host, then run:

```sh
python3 verifier/actions/publish-build.py \
  --run /path/to/completed-run --profile /path/to/profile.json \
  --libraries /path/to/libraries.json --key /path/to/host-signing-key.pem \
  --out /path/to/cache-output --publish
```

The signing key and GitHub credentials stay on the host. The public key is pinned
in `verifier/standard/build-cache-public.pem`; key rotation requires updating that
pin. The publisher accepts locally produced worker records supplied by the server
operator. Submitter-provided files must go through the isolated source build.
