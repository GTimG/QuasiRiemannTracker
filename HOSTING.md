# Running and hosting the website

## Run locally

Use Node.js 22.17 or later. Repository checks also require Python 3.

```sh
npm ci
npm run dev
```

The site runs at `http://127.0.0.1:4173`. `npm run build` creates the static site
in `dist/`; `npm run preview` serves that build. Run `npm run check` to run the
tests and production build.

## Hosting

GitHub Actions builds and deploys `main` to GitHub Pages. For another static
host, run `npm run build` and publish `dist/`. Set `QRH_BASE_PATH` to the site's
URL prefix when hosting under a subdirectory.

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

## Verification infrastructure

These notes are for maintainers who operate the verification workflows.

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
the infrastructure-failure fallback. Keep branch protection requiring `test`, `website`
and `qrh/pr-admission`, with verifier and registration updates reviewed by maintainers.

### Build cache

Admission restores previously compiled submission modules from a signed build
cache, so a PR compiles only its own new modules. The **Build cache** workflow
maintains it after every push to `main` that changes `submissions/` or the
verifier, and rebuilds all shards every Monday at 04:47 UTC. On the proof runner it compiles the shared `Submissions.<id>.*`
modules of every merged submission in the same sandbox as admission, and
publishes each submission (a logical shard) as bounded archive pieces to the
`submission-build-cache-v2` release, listed in a signed `cache.json`. Only
shards whose modules changed are rebuilt on pushes; admission downloads only the shards
its PR imports. Each PR's `Candidate.*` modules are never cached.

Large shards are split using actual compiled file sizes. Each piece holds at
most 512 MiB of compiler outputs, keeps a module's companion files together,
and must compress below 1 GiB. The unchanged 4 GiB extraction and file-count
limits still apply independently to every archive. The signed version-3 index
binds every piece's hash, size and exact module keys; missing, overlapping or
misassigned pieces fail validation before publication. Version-2 caches remain
readable and are rebuilt into the new format on the next cache run.

The signing key is the `QRH_BUILD_CACHE_KEY` secret of the `build-cache`
environment, restricted to `main`; its public key is pinned in
`verifier/standard/build-cache-public.pem`. A short hosted preflight checks the key
against that pin before starting the expensive build. The proof-runner job has
read-only repository access and no environment secrets. It passes compressed
shards as data to a separate hosted publication job, which checks the commit,
build inputs, module keys, archive paths and hashes before signing. The publisher
also downloads and authenticates its published index and changed archives. A cached module cannot make
a proof pass: Comparator and all three kernels re-check every exported
declaration. Key rotation requires updating the pin.

For a manual refresh, open **Actions → Build cache → Run workflow**, choose
`main`, and optionally select **Rebuild every shard**. Without that option,
unchanged authenticated shards are reused. The weekly rebuild does not reuse
compiled submission shards, but still restores the pinned upstream dependency
cache. Only `main` can run the signing preflight and publication jobs. Keep the
environment's deployment branch rule limited to `main`, and keep Actions enabled
for scheduled runs. A successful run ends with both signature verification and
the public-download check; a successful compile alone is not publication.

## License

Project code is licensed under [Apache-2.0](LICENSE). Third-party proofs and
dependencies retain their original licenses and attribution; see [NOTICE](NOTICE).
