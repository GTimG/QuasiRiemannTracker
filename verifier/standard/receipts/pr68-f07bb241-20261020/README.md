# Independent maintainer verification of PR #68

The exact source at `f07bb2418990a9976c0da5f65bb6a7a77da94c9a` passed verification at
2026-10-20T23:12:52.462554+00:00. The bound is `8748087/10000000` (0.8748087), for the
canonical all-moduli, all-Dirichlet-character statement.

The original [worker receipt](result.json), SHA-256
`9c7b0a2077fcb2c7d5921ede1125da63bde5f393463593469190df14f9930c45`, was generated outside the candidate's writable
environment. It was retrieved over authenticated SSH and checked against the
immutable source, dependency trees, canonical challenge, pinned tools and logs.
[The kernel log](judge.log) records Comparator and Lean, NanoDa and con-ron
acceptance. Only `propext`, `Classical.choice` and `Quot.sound` were permitted.

All 4,663 modules in the necessary submission import closure were compiled
fresh, including the OpenAI source dependency. No candidate compilation cache
or old OAI objects were reused. The 44,577 non-OAI runtime files
were obtained from fresh pinned dependency trees, the official Mathlib cache
and protected compatibility patches, then copied into a private library with
before/after hash checks. This includes all compiler IR files. Every package
source tree was compared with its exact pin and protected patch; see
[fresh-package-audit.json](fresh-package-audit.json). The complete exported proof
was checked by three kernels. Package pins and compatibility patches are unchanged.
Compiler/exporter bootstrap trust remains a limitation.

The unprivileged ETH worker used Palomar's real sandbox with no network, private
home and temporary directories, read-only source/libraries, and resource limits.
Filesystem/network, positive-proof, changed-statement and ill-typed-proof controls
passed. The canonical challenge was exported before candidate execution and its
hash remained unchanged. The operator service was limited to 16 CPU threads and
128 GiB of memory, retaining the driver's 75%/85% effective-worker memory
thresholds. The independent kernels ran serially.

The verifier was taken from protected revision
`d6103b24af1e98b72bdba1044c1dad6f48d5b902`, with exactly two time-budget changes:
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

The [hosted admission attempt](https://github.com/GTimG/QuasiRiemannTracker/actions/runs/39459276356)
hit its memory ceiling while running Lake (exit 137, oom-kill).
[The saved failure summary](hosted-resource-failure.json) records resource
exhaustion rather than mathematical rejection. This independently accepted run
can be registered through the existing protected local-receipt process.

The first ETH preflight stopped before candidate compilation because its shared
verifier checkout had missing tracked files. The successful replay used a fresh
private archive of the same pinned Palomar commit, authenticating all 85 source
files before importing the verifier. The shared checkout was left untouched;
all checker binary pins remained identical. A second preflight identified a
missing shared runtime library; the exact checksum-pinned checker release was
restored privately before the successful replay. The snapshot's manifest digest is
recorded in orchestration-provenance.json. A third attempt stopped on a
compiler error reproduced by a standalone maintainer-written rational function
without any candidate imports. Rebuilding the complete pinned library environment
resolved that diagnostic. The successful replay used the unchanged candidate
source and freshly compiled its full import closure. Failed-attempt evidence
is retained privately; none of those failures was treated as proof acceptance.

This record cannot approve changed source or override a mathematical rejection.
Original authorship, Apache-2.0 and inherited notices are preserved. Verification
timestamps are separate from PR submission time and do not assert discovery priority.
