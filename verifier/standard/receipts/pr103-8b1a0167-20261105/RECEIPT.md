# RECEIPT — Local rebuild + kernel receipts, quasi-Riemann 7/8 baseline rung (openai-baseline)

**Verdict: PASS (local rebuild OK).** The full openai-baseline import closure — all 2,927
vendored submission modules + the canonical challenge + the solution wrapper — compiled
from source under Lean v4.34.1 against Mathlib `d13f23b7` on macOS arm64, and
`#print axioms` for every target declaration returns exactly `[propext, Classical.choice,
Quot.sound]`. Zero compile errors. Within the 4 h budget (successful run: 3 h 00 m 51 s).

Generated 2026-11-04 by a bounded local rebuild lane. Receipt generation only — no
submission, no external posts/issues/PRs/comments. Conventions follow
GTimG/QuasiRiemannTracker `verifier/standard/receipts/*` (README.md + result.json shape),
adapted for a LOCAL run; machine-readable twin: `result-local.json`.

## 1. Target

Board: bigospeedrun.com/other/quasi-riemann, OpenAI 7/8 baseline row (θ = zero-free
half-plane Re s > θ for ALL Dirichlet L-functions; lower better; GRH = 1/2).
Canonical statement: `QRH.canonical_bound` (rendered from `verifier/upstream-challenge.lean`
per `core/standard-challenge.mjs`, θ = 7/8). Proof chain: `QRH.canonical_bound` :=
`Candidate.bound` := `Submissions.openai_baseline.bound` :=
`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` :=
`SevenEighths.ProbeFinalAssemblyUnconditional.dirichlet_nonzero`.

## 2. Pins and provenance (byte-verified)

| Item | Value |
|---|---|
| Tracker | GTimG/QuasiRiemannTracker @ `47134867e2ce4d4a311d2da93783c2ae721d9bb9` (HEAD 2026-11-03) |
| Baseline tree | `submissions/2026-10-06-openai-baseline` git tree-sha `e2278f8d3de178f616b8a03c972caabbf2d874501` |
| Upstream | openai/math @ `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (= pins.json; Apache-2.0) |
| Lean / Lake | `leanprover/lean4:v4.34.1` (elan), Lake 5.0.0-src+5045d00 |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` — warm exact-pin oleans APFS-cloned (`cp -c`, 8.9 GB in 51 s) from `/tmp/sssp_audit/build/.lake/packages`; original never written |
| PrimeNumberTheoremAnd | `c39a751132c88b6e8080b74c74023fd95b3d8be0` + `PrimeNumberTheoremAnd-lean4341.patch` sha256 `0890432340c0025973bcfe070b634355fa366cc831595f68526e4c73c8903d82` |
| rellich-kondrachov | `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23` + `rellich-kondrachov-lean4341.patch` sha256 `0c121d8517dfeadc93ef24fe2deb56beec7cb3998e2552dee8f61c780b1408c8` |
| Scaffolding | `verifier/standard/lakefile.lean` (blob `86cbb08d7274ef9827e2d7809abcdba9ec4c683a`), `verifier/standard/lake-manifest.json` (blob `38400d31f072a8d417078fdf0a064e1577d310da`) — blob-exact copies |
| Challenge template | sha256 `8fb13ad977bca104591fcbc6ef01a58496e7385053c9b1445f95749afc0eff54` = `pins.json.challenge_sha256` ✓ |
| Rendered `Challenge.lean` | sha256 `a9d290c74920624ba06f66da0a56b633876e2a0ac230613add78b61370fbfe12` — **byte-identical to pr69 receipt `BaselineChallenge.lean`** ✓ |
| Rendered `Solution.lean` | sha256 `704bccefad1dfc92056eefec4b5cbe1a22c0f9a7dc1ea72e803402fe48cde476` (solutionWrapper recipe: `exact Candidate.bound χ hs hpole`) |
| `Candidate/Main.lean` | sha256 `5f66b7a2b97194d63ee10da833d5c42a36c7c9656bab83e5f79e9b1dac9aa5ab` = git blob ✓ |
| `Submissions/openai_baseline/Main.lean` | sha256 `a8d7cf4dbf1ee1eafda295a78f03a926975f52236997bc2f64c4ccb2f86b6bbc` |
| vendored `OAI/.../DirichletL/Nonvanishing.lean` | sha256 `357e3a752ef6311d0be98dd45ac0ab6d38614d442732511e78b815c036f3a48e` |
| vendored `OAI/.../Detector/FinalAssemblyUnconditional.lean` | sha256 `160ac51d898d8cce6aec7d2d4226cc8ff1b03dec51e4c57bce12b3183f19c0dc` |
| vendored `OAI/.../DirichletL/Foundation.lean` | sha256 `32d208a7dc588ee87127a75e81ee4f33aedb744e9fa63b7b49f7612c06e2456a` |

**Full-tree upstream verification:** all 2,926 vendored `OAI/**.lean` modules compared
against openai/math@`fd4aeeb2` `lean/OAI/**` (blob-extract via `git fetch --depth 1` +
`git archive`): **0 missing, 0 mismatches** modulo exactly two documented packaging
transforms — CRLF→LF (upstream stores CRLF blobs) and import remap `import OAI.` →
`import Submissions.openai_baseline.OAI.`. Harness: `verify_upstream.py`.
The tracker's two lean4341 patches are **byte-identical to upstream's own
`lean/patches/` copies** (LF-normalized) and were applied with the worker's own
idempotent `git apply` mechanism (`verifier/actions/setup.py`). Unpatched RK `70f85d4`
provably fails on Lean 4.34.1 (preserved: `build.log.rkfail`) — the patches are
load-bearing, and this receipt demonstrates the failure they cure.

## 3. Build record

Host: Apple M4 Max 128 GB, macOS, chronically loaded (other tenants: 1-min loadavg
54–435 peak during the run; swap free dipped to 592 MB; host-wide lean/lake RSS peaked
90 GB including a concurrent foreign lane — this lane itself capped at 4 threads).
Monitor: `hostmon.log` (130 samples, 120 s cadence). No OOM, no abort, no wedge.

Parallelism: `LEAN_NUM_THREADS=4` — Lake 5.0.0 has no `-j` flag (maintainer-documented:
the env var is the mechanism; the tracker worker itself uses it, `setup.py`). Cap honored.

Phases (all logs preserved):
1. `build.log.abort1/abort2` — `-j`/`--jobs` option errors (Lake 5); fixed via env var.
2. `build.log.rkfail` — unpatched RK type-mismatch errors (see §2); patched, resumed.
3. `build.log` — **final run 19:31:39Z → 22:32:30Z (3 h 00 m 51 s)**:
   - `lake build Challenge` — exit 0 (19:31:52Z; first pass 19:12:47→19:15:29Z,
     8,925 jobs, 2 m 42 s). Warm Mathlib: **zero recompiles**; only warning = the
     template's intentional `sorry` (Challenge.lean:6:8).
   - `lake build Solution` — **exit 0 (22:32:30Z), 7,065 jobs, 0 error lines.**
   - Supplement 23:31–23:33Z: `lake build Submissions` added the 2 Hecke-statement
     modules outside the Dirichlet entrypoint closure (~7 s each).
   - Final inventory: **2,930 root-package oleans = 2,927/2,927 submission modules +
     Candidate.Main + Solution + Challenge** (`final-stats.json`, `built-modules.txt`).
   - Module timing (n=2,805 timed jobs): median 8.3 s, p90 23 s, max 85 s;
     531 compiler-minutes total ≈ 3 h wall at effective ~3 of 4 lanes under host load.

## 4. Kernel receipts (`#print axioms`, Lean 4.34.1 default kernel, local oleans)

All eight declarations — **axioms exactly `[propext, Classical.choice, Quot.sound]`,
no `sorryAx`, no others** (logs: `axioms.log`, `axioms_zeta.log`, `axioms_hecke.log`):

1. `QRH.canonical_bound` (Solution.lean — the canonical all-Dirichlet θ=7/8 statement)
2. `Submissions.openai_baseline.bound`
3. `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` (metadata entrypoint)
4. `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` (zeta corollary)
5. `OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re`
6. `OAI.SevenEighths.HeckeFamily.LFunction_ofResidue_ne_zero_of_seven_eighths_lt_re`
7. `OAI.SevenEighths.HeckeRayFamily.LFunction_ne_zero_of_seven_eighths_lt_re`
8. `OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_certified_bands`

Matches the hosted permitted-axiom set (pr69 receipt `allowed_axioms`). Scope note,
honest: this is the Lean default kernel checking locally-rebuilt oleans — NOT the
worker's frozen lean4export + Lean/NanoDa/con-ron triple-kernel pipeline (Linux-pinned
binaries). The "local changes" warnings on PNT+/RK during probes are the applied
compatibility patches.

## 5. Board arithmetic cross-checks (exact, Decimal-50)

- 7/8 = 0.875 exactly (binary rational; float-exact `7/8 == 0.875`).
- Bebel top = (777 − √1081)/852 = 0.87338196661320751992902677864237186940501558853491.
- Gap = 0.875 − (777−√1081)/852 = 0.00161803338679248007097322135762813059498441146509
  ≈ 1.618×10⁻³. The baseline rung is WEAKER than the top row: it establishes the empty
  **Lean Verified tier** (independent local rebuild + kernel receipts), not the record.

## 6. Environment quirks (reproducibility notes)

- Host `git` checkout applies LF→CRLF conversion even with local `core.autocrlf=false`
  (global config sets `true`; forced `checkout-index` still converted). All staging used
  **git blob extraction** (`git archive`/`cat-file`, conversion-free) — the worker's own
  "read Git blobs as data" semantics (`prepare.mjs`). Every staged file hash-verified.
- Lake 5.0.0 parallelism: `LEAN_NUM_THREADS` (no `-j`/`--jobs` exist).
- Warm Mathlib reuse works cross-workspace: lake trace validation accepted the cloned
  8.9 GB exact-pin build with zero recompiles (revisions identical in both manifests).

## 7. Artifact index (/tmp/qr_rebuild/)

`workspace/` (resumable QRH lake workspace, fully built) · `build.log` +
`build.log.{abort1,abort2,rkfail}` · `axioms.log`, `axioms_zeta.log`, `axioms_hecke.log` ·
`hostmon.log` · `final-stats.json` · `built-modules.txt` · `dep-revs.txt` ·
`verify_upstream.py` + `openai-src/lean` (upstream comparison inputs) ·
`stage_workspace.py`, `run_build.sh`, `final_stats.py` · `tracker/` (reference clone) ·
`RECEIPT.md`, `result-local.json`.

No writes outside /tmp/qr_rebuild/. /usr/bin/git used for all git operations.
