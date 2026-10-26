# Independent maintainer verification of PR #66

The exact source at `c68a3b2ba5b28b9c9b4bf26966ed6ee04ffa29b9` passed verification at
2026-10-19T18:54:39.570286+00:00. The bound is `874828524351/1000000000000` (0.874828524351), for the
canonical all-moduli, all-Dirichlet-character statement.

The original [worker receipt](result.json), SHA-256
`b30fc3ffe7065070dd66eaea8239f07464de852afc1a3274cd7e708e7dc0e8a3`, was generated outside the candidate's writable
environment. It was retrieved over authenticated SSH and checked against the
immutable source, dependency trees, canonical challenge, pinned tools and logs.
[The kernel log](judge.log) records Comparator and Lean, NanoDa and con-ron
acceptance. Only `propext`, `Classical.choice` and `Quot.sound` were permitted.

All 4,479 modules in the necessary submission import closure were compiled
fresh, including the OpenAI source dependency. No candidate compilation cache
or old OAI objects were reused. The 34,945 approved non-OAI package objects
were copied into a private library after matching the previously authenticated
inventory. The complete exported proof was checked by three kernels. Package
pins and compatibility patches are unchanged from that approved snapshot.
Compiler/exporter bootstrap trust remains a limitation.

The unprivileged ETH worker used Palomar's real sandbox with no network, private
home and temporary directories, read-only source/libraries, and resource limits.
Filesystem/network, positive-proof, changed-statement and ill-typed-proof controls
passed. The canonical challenge was exported before candidate execution and its
hash remained unchanged. The operator service was limited to 16 CPU threads and
128 GiB of memory, retaining the driver's 75%/85% effective-worker memory
thresholds. The independent kernels ran serially.

The verifier was taken from protected revision
`9c0e14f985041e397f71c574028193ee595a0f98`, with exactly two time-budget changes:
the shared deadline was raised from three to eight hours, and the final judge
timeout from one to four hours. See [the complete patch](budget-only.patch) and
[original component hashes](orchestration-provenance.json). No acceptance,
axiom, sandbox or tool-pin policy was changed. Palomar was pinned to
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`; source Lean was 4.34.1, with the
pinned 4.35.0-rc2 checker toolchain. See [driver](replay-driver.txt),
[tool pins](tool-pins.json), [dependency pins](dependency-pins.json),
[challenge audit](challenge-audit.json) and [audit](audit.json).

[logs.json](logs.json) preserves all compilation and checker logs. Hashing each
UTF-8 value reproduces its receipt artifact digest. Large exports and host-specific
inventories remain in the maintainer's private evidence store; their hashes are
preserved in the original receipt. [Challenge.lean](Challenge.lean) is a statement
template whose intentional `sorry` is not a proof. Acceptance applies to the
checked [solution](Solution.lean).

The [hosted admission attempt](https://github.com/GTimG/QuasiRiemannTracker/actions/runs/39255000018)
exhausted its shared three-hour deadline while compiling
`Candidate.Uneven.MainPhysicalCompletePayment`. Candidate compilation did not complete, and the final
comparison/kernel stage was not reached. [The saved failure summary](hosted-resource-failure.json)
records a timeout, not a mathematical rejection. This independently accepted run
can be registered through the existing protected local-receipt process.

This record cannot approve changed source or override a mathematical rejection.
Original authorship, Apache-2.0 and inherited notices are preserved. Verification
timestamps are separate from PR submission time and do not assert discovery priority.
