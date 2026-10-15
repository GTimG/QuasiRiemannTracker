# Independent verification of PR #48

The exact prepared revision `57ca0662b4ddeb2a75c0e302d0350cc65cf67c12`
passed independent verification at 2026-10-14T22:27:39.365341+00:00, for
`437429/500000` (0.874858) in the canonical all-moduli, all-Dirichlet-character
statement. [The original receipt](result.json) has SHA-256
`5ea32e372c258299711c6a66fab0391de938150261b76cfe274306ba63e61b64`. [The kernel log](judge.log) records Comparator,
Lean, NanoDa and con-ron acceptance. Only `propext`, `Classical.choice` and
`Quot.sound` were permitted.

All 3,808 required Lean modules, including the complete necessary OpenAI source
dependency, were freshly compiled in the immediately preceding check of
`f7ec5c9559b3dec590bda3834c18c49494b9ea81`. That full proof also passed all
three kernels at 2026-10-14T21:56:52.248722+00:00; see its unmodified
[receipt](source-build-result.json), [source contract](source-build-contract.json)
and [complete compilation/checker logs](source-build-logs.json).

Main advanced during verification. Its historical-certificate migration changed
the baseline metadata, which is included in the publication dependency hash.
The prepared revision merges that main revision without changing any Lean source.
[Source equivalence](source-equivalence.json) records the sole changed prepared
file, `dependencies/openai-baseline/metadata.json`; the generated challenge,
wrapper, import graph and all 3,808 Lean files are unchanged.

The final run reused the authenticated preceding compilation archive only after
every module fingerprint matched: source bytes, imported module fingerprints,
compiler, library inventory and compilation recipe. It then repeated sandbox
controls, positive/wrong-statement/ill-typed-proof controls, independently froze
the trusted challenge, exported the solution and reran Comparator and all three
kernels. [Cache provenance](cache-provenance.json) binds the preceding accepted
receipt and archive digest. Authentication is through the maintainer's SSH
session and outside-sandbox records; no public server-signing-key attestation
is claimed for this private compilation archive.

The unprivileged Linux workers used Palomar's real sandbox, with no network,
private home/temporary directories, read-only source and approved libraries,
and resource limits. The trusted challenge was exported before candidate
execution and remained unchanged. Receipts were generated outside the
candidate's writable environment. Both workers had 16 CPU threads and a 128 GiB
service memory limit. The protected replay retained 75%/85% effective-worker
memory thresholds, a three-hour total budget and a one-hour judge budget.
Independent kernels ran serially. No mathematical check was omitted.

The final protected verifier revision is
`afabe6f0909ef2bf74d12a3d25608a473d3ff5b2`; the fresh source-build verifier was
`5cdfac0694c2d96635e324c595e0f7d3d3074a83`. Both unmodified drivers are retained.
The newer driver adds an exclusive compilation retry for memory exhaustion;
the challenge, dependency pins, kernel policy and checker binaries are unchanged.
Palomar is pinned to `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, with source
Lean 4.34.1 and the pinned 4.35.0-rc2 checker toolchain.

The 34,945 non-OAI package objects were rehashed against the prior authenticated
PR43 inventory before being copied to each private worker. No old OAI object
library was reused: the required OAI modules were built from source. Compiler
and exporter bootstrap trust remains a limitation. See [audit](audit.json),
[tool pins](tool-pins.json), [dependency pins](dependency-pins.json) and
[challenge audit](challenge-audit.json).

[GitHub's hosted attempt](https://github.com/GTimG/QuasiRiemannTracker/actions/runs/38626415925)
exhausted its memory ceiling while running Lean (`exit 137`, `oom-kill`).
[Its saved check summary](hosted-resource-failure.json) records a resource failure,
not mathematical rejection. This independently accepted result can be registered
through the existing protected local-receipt process.

[logs.json](logs.json) and [source-build-logs.json](source-build-logs.json)
preserve exact UTF-8 log contents; hashing each value matches its original receipt
artifact digest. Large exports and the compilation archive remain private, with
their hashes retained in the receipts. [Challenge.lean](Challenge.lean) is a
statement template: its intentional `sorry` is not a proof. Acceptance applies
to the independently checked [solution](Solution.lean).

This record is bound to the exact prepared revision, rational and dependency
snapshot. It cannot approve changed source or override a mathematical rejection.
Authorship and Apache-2.0 notices are preserved. Verification dates remain
separate from PR submission time and do not assert mathematical discovery priority.
