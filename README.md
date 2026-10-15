# Quasi-Riemann Tracker

Live: [gtimg.github.io/QuasiRiemannTracker](https://gtimg.github.io/QuasiRiemannTracker/)

Quasi-Riemann Tracker follows bounds on the real parts of zeros of Dirichlet
L-functions. The timeline and leaderboard show exact bounds, authors, sources,
and verification status. Smaller bounds are stronger; the generalized Riemann
hypothesis corresponds to a bound of $1/2$.

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

Each `submissions/<result-id>/` directory contains `metadata.json` and its Lean
source in `src/`. Website deployment combines this metadata with
merged admission records to generate the catalogue. Generated catalogue JSON is
ignored by Git. Local development and preview builds generate the same files.
Builds generate small verification records in `public/certificates/` that link
each checked bound to its source commit and verification report. These files are
ignored by Git. Historical report URLs and hashes live in the corresponding
submission's `metadata.json`; new submissions use their admission records.

Verified PR contributions are plotted at their PR submission time. Older
entries without a recorded PR submission date retain their documented date
and label; a submission date is not a mathematical discovery date. Verification
and merge dates are shown separately in the details. Metadata comes from the
latest admitted version before merge, while the first verification date and
linked certificate come from the earliest authenticated success for the same
PR head, bound and source tree. Metadata edits and reruns cannot reset that date.
The offline admission cache retains all eligible receipts; refresh it through
the normal online main-branch build to recover older receipts from the archive.

## Submit

1. Start from the current `main` branch. Add Lean source under
   `submissions/<result-id>/src/Candidate/`, with theorem
   `Candidate.bound` in `Main.lean`. Use the pinned dependencies in
   [verifier/pins.json](verifier/pins.json) and
   [verifier/standard/lake-manifest.json](verifier/standard/lake-manifest.json).
2. **Commit `submissions/<result-id>/metadata.json` alongside the Lean source.**
   Admission reads this required file from the exact PR head. The submission
   directory contains:

   ```text
   submissions/example-bound/
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
     "dependencies": ["openai-baseline"]
   }
   ```

   Required fields are `title`, `authors` (a nonempty array of objects with
   `name` and an optional HTTPS `url`), and `description`. The description
   explains the method and credits previous work.

   Declare each directly imported submission in `dependencies`, using its
   directory name under `submissions/`. It defaults to an empty list.
   `builds_on` records attribution to existing result IDs; `dependencies`
   supplies the source modules available to imports.

   The other supported fields are `license` and `references` (an array of
   objects with `label` and HTTPS `url`). The
   [metadata validator](verifier/submission-metadata.mjs) defines the field
   formats and size limits.

3. Open a PR using the [submission template](.github/PULL_REQUEST_TEMPLATE.md).
   Start its body with the result ID, exact bound, and decimal approximation.
   The result ID must match the submission directory name:

   ```text
   QRH-Result: example-bound
   QRH-Bound: 7/8
   QRH-Decimal: 0.875
   ```

   Use a reduced fraction or supported exact algebraic expression for
   `QRH-Bound`. Give an accurate truncated `QRH-Decimal` with enough digits
   to differ from the current best verified bound.
   Equal bounds accept any supported decimal precision. These PR fields declare
   the bound; the committed `metadata.json` supplies its publication metadata.

4. GitHub Actions checks the exact PR head, including drafts. Comparator checks
   the statement and allowed axioms against the
   [canonical target](verifier/upstream-challenge.lean), with the submitted bound
   substituted for $7/8$. Lean, NanoDa, and con-ron must all accept the proof.
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
their importers compile again. Every result still runs Comparator and all three
kernels. An unavailable or incompatible cache triggers a source build.

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
