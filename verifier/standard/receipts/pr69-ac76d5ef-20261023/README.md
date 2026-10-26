# Independent verification of PR #69

Source `ac76d5ef6008d976a7b8f3c1d921af2317e79ce9` passed at 2026-10-22T22:13:39.013693+00:00. It proves the canonical
all-Dirichlet statement for `8747729897/10000000000` (0.8747729897), with the
original moduli, characters, pole exclusion and L-function. The intentional
`sorry` in [Challenge.lean](Challenge.lean) is only the statement template.

[judge.log](judge.log) records Comparator acceptance and independent acceptance
by Lean, NanoDa and con-ron. Only `propext`, `Classical.choice` and `Quot.sound`
were permitted. The original [receipt](result.json), SHA-256
`b9976aad6617832a1140abcfa903bb2fa06c736e5578940ae5a814ef2a3fc877`, was generated outside the candidate sandbox. It was
retrieved through authenticated SSH and checked against all 6,477 source-file
hashes reconstructed directly from immutable Git objects, the dependency trees,
library inventory, frozen exports, checker binaries and logs.

## Checker version and resource history

The bundled NanoDa exhausted its 31-bit expression-index capacity. A widened-index
diagnostic then exposed excessive temporary expression growth in arithmetic
lemmas. Neither failed attempt is proof acceptance. The accepted check uses
**unmodified upstream NanoDa 0.4.26**, commit
[`998e0a84e4c1572ca279ff05007af6ec6639405a`](https://github.com/ammkrn/nanoda_lib/tree/998e0a84e4c1572ca279ff05007af6ec6639405a),
with the exact source manifest and binary hash included here. No local storage
patch is used in the accepted check. All other checker binaries retain the
protected toolchain hashes. This is an explicit maintainer-reviewed local
checker upgrade; the hosted workflow's tool pins were not silently changed.

The upstream source passed 54 tests (zero failures; eight documentation tests
ignored upstream) and built offline from its locked dependencies. The actual
OpenAI seven-eighths baseline passed Comparator and all three kernels using this
same runtime: see [baseline-judge.log](baseline-judge.log). Fresh sandbox controls
and positive, mismatched-statement and ill-typed-proof controls passed. Hidden
assumptions and `sorryAx` were explicitly rejected. The upstream source is
Apache-2.0; its [license](NANODA-LICENSE) is preserved.

The first combined evaluation exceeded a 40-minute deadline, without OOM. The
accepted resource-only retry retained the proof, checker binaries and comparison
configuration, with an eight-hour judge limit and 64 GiB worker memory ceiling.
A separate full-export NanoDa measurement completed in 268.947 seconds with
6,318,489,600 bytes peak cgroup memory; this is not the peak of the whole pipeline.

## Source, sandbox and limitations

The original run freshly compiled all 6,471 required submission and OpenAI
modules. No candidate/OpenAI object cache was reused for that build. The kernel
retry used the same authenticated frozen exports, rather than rebuilding the
unchanged modules. The trusted challenge was exported before adversarial sources
executed and independently regenerated to the same digest. Approved non-OAI
dependencies were copied into a private library and authenticated before and
after verification. Compiler/exporter bootstrap and approved library provenance
remain part of the trust model; testing is not a proof that kernel software has
no bugs. All three independent kernel checks remain required.

Protected project revision: `b3c157e2e1278b7690eda65499bf9974dc59950c`.
Palomar: `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.
Source Lean: 4.34.1. Comparator/checker runtime: 4.35.0-rc2 with the explicit
NanoDa replacement above. Checking used real unprivileged Linux isolation,
no checking network, private writable scratch, read-only inputs, no credentials,
and bounded resources. Source, library and tool identities were checked again
after successful kernel completion.

## Evidence and reproduction

Use the exact source/dependency/checker pins, freshly compile the approved source
closure in the protected sandbox, and export the trusted canonical challenge
before any candidate elaboration. Build the pinned NanoDa from its Cargo.lock
using `cargo test --locked --offline` and `cargo build --release --locked --offline`
after separately fetching its locked dependencies. Use a private build directory
and replace only NanoDa in a private copy of the pinned runtime. Reproduce the
sandbox/rejection controls and real baseline, then run Comparator with all three
kernels over the authenticated challenge and solution exports. Never use a
candidate-supplied challenge, toolchain, cache or receipt.

[logs.json](logs.json) includes compilation and checker logs. Only private
filesystem paths are removed in public log copies; [log-redactions.json](log-redactions.json)
records original/public hashes. Large exports, host inventories and original
orchestration sources remain private and are bound by hashes. The raw receipt
also hashes its pre-final status, attempt and worker-log snapshots before writing
PASS; [pre-final-snapshot-audit.json](pre-final-snapshot-audit.json) distinguishes
these from the final files. Those bookkeeping snapshots are not proof evidence.

All 316 project tests and the production build passed during source review.
Authorship, inherited notices and licenses are preserved. Verification time is
separate from PR submission and discovery. Publication and merge additionally
require the exact-head local registration and authenticated protected admission.
