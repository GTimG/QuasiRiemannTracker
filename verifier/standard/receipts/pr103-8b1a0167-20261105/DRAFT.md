# Draft issue body (PREPARED — not filed; coordinator reviews and files)

Suggested title: `Independent local rerun of the openai-baseline (7/8) rung — receipts offered for maintainer review`

---

Disclosure up front: this report was prepared by an AI-authored lane of the darkhipo
swarm, working under a receipts-first policy. Nothing was posted by automation; a human
reviewed and filed this. We have no submission to the board and claim no result — this
is verification evidence offered to the project, freely reusable under the same terms
the tracker itself uses (Apache-2.0 where applicable; upstream mathematics remains
OpenAI's).

## What was rerun

The vendored OpenAI seven-eighths baseline (`submissions/2026-10-06-openai-baseline`,
result id `openai-baseline`) was rebuilt **from source, end to end**, outside CI, on
different hardware and OS from the hosted workers: Apple M4 Max (128 GB, macOS arm64),
chronically loaded by unrelated concurrent workloads during the run.

Pins (all byte/rev verified before build):

- GTimG/QuasiRiemannTracker @ `47134867e2ce4d4a311d2da93783c2ae721d9bb9`
- baseline tree `e2278f8d3de178f616b8a03c972caabbf2d874501`
- openai/math @ `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
- Lean `v4.34.1` / Lake 5.0.0-src+5045d00, `LEAN_NUM_THREADS=4` (the mechanism
  `verifier/actions/setup.py` itself uses; Lake 5 has no `-j`)
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (warm exact-pin oleans,
  APFS-cloned; zero Mathlib recompiles — lake trace validation accepted the cache)
- PrimeNumberTheoremAnd `c39a751…` and rellich-kondrachov `70f85d4…`, each with the
  tracker's lean4341 patch applied via the worker's own idempotent `git apply` recipe
- workspace scaffolding = blob-exact copies of `verifier/standard/lakefile.lean` and
  `lake-manifest.json`

## What passed

- `lake build Challenge`: exit 0 (8,925 jobs). Our rendered canonical challenge (θ=7/8,
  `core/standard-challenge.mjs` recipe) is **byte-identical to `BaselineChallenge.lean`
  in `verifier/standard/receipts/pr69-ac76d5ef-20261023/`**
  (sha256 `a9d290c74920624ba06f66da0a56b633876e2a0ac230613add78b61370fbfe12`).
- `lake build Solution` (+ `Submissions` supplement for the two Hecke-statement modules):
  exit 0 (7,065 jobs), **0 errors**, **2,927/2,927** submission modules compiled from
  source; 3 h 00 m 51 s wall under a 4-thread cap; median module 8.3 s, max 85 s.
- `#print axioms` (Lean 4.34.1 default kernel) for **eight** declarations —
  `QRH.canonical_bound`, `Submissions.openai_baseline.bound`, the Dirichlet and zeta
  `…ne_zero_of_seven_eighths_lt_re`, and the four Hecke statements — each returns
  exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no extras.
- Provenance: all 2,926 vendored OAI modules **blob-verified** against
  openai/math@`fd4aeeb2` (0 missing, 0 mismatches modulo the two documented packaging
  transforms: CRLF→LF and the `Submissions.openai_baseline.` import remap). The tracker's
  two lean4341 patches are byte-identical to upstream's own `lean/patches/` copies.
- Negative control: unpatched rellich-kondrachov fails elaboration on these exact pins
  (preserved log) — the build demonstrably exercised the real pinned dependency path.

## Honest limits

- **Lean default kernel only.** No lean4export freeze, no NanoDa, no con-ron (their
  binaries are Linux-pinned and protected). This rerun does not replicate, and does not
  ask to replace, the triple-kernel acceptance in `verifier/standard/receipts/`; it has
  no `contract.json`/`controls.json`/`tool-pins.json` analogues.
- Per README "Reuse an independently verified receipt" (L207–244): authentication is
  maintainer-reviewed evidence plus protected registration, and "a hash or a
  candidate-written PASS alone is not authentication" — this bundle is offered strictly
  as maintainer-reviewable evidence, with no registration claim. We have not touched
  `verifier/` and cannot (L226: "Candidate PRs cannot edit the verifier or register results").
- The host carried heavy foreign load throughout (1-min loadavg peaks to 435; swap free
  dipped to ~0.6 GB). This bounds wall-time claims only; compilation is per-module and
  every module here compiled from source in this workspace. Samples included.
- Platform difference (macOS arm64 vs hosted Linux x86-64) is the point of an
  independent rerun — and also means artifacts are not interchangeable with worker caches.

## What we suggest (maintainer's call entirely)

If useful, this could serve as evidence toward the site's uniform "No independent
rerun" note for the baseline row, in whatever form the project prefers — a referenced
archive, a receipt-directory entry under your own conventions, or nothing at all. The
bundle (recipe scripts, rendered sources, all logs, hashes, host samples; sha256
manifest included) is attached/linked at the filer's discretion. The full built
workspace was retained on the rerun host and can revalidate incrementally or re-run any
probe on request.

Credit where due: this was only possible because the tracker's conventions — pinned
manifests, the vendored baseline, the standard worker recipe in `verifier/standard/`,
and the published receipts with their baseline artifacts — make an independent rerun a
mechanical exercise. Thank you for building it that way.
