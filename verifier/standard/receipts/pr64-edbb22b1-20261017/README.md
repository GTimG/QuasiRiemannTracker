# Local verification of PR #64

Commit `edbb22b1a080c961b19e438e9e8ce6d6b3842739` passed at 2026-10-17T23:31:58.056623+00:00 for the canonical
all-moduli, all-Dirichlet-character bound `874835173/1000000000` (0.874835173).

The [worker receipt](result.json) has SHA-256
`590991f6564dc9e5b012d947e554354c8c0c8fa042a304a941b564cff020ceff`. [Comparator and all three kernels](judge.log)
accepted the exported proof with only `Classical.choice`, `Quot.sound` and
`propext` permitted. Sandbox, statement-mismatch and ill-typed-proof controls passed.
The canonical challenge was exported before candidate execution.

The local KVM worker compiled all 913 submission modules and reused 2,923
OpenAI dependency modules from the authenticated build cache recorded in the
receipt. The complete exported proof was checked by Lean, NanoDa and con-ron.
Source hashes, dependency trees, tool pins and library inventories were checked.
The VM had 12 CPUs and 32 GiB of RAM. The orchestrator used a 30 GiB memory
budget; compilation used 11 slots and
memory-heavy modules retried exclusively. Kernels ran serially. During con-ron,
the soft memory threshold was raised from 22.5 GiB to the existing 25.5 GiB
hard cap after sustained reclaim throttling; see [the adjustment record](judge-memory-adjustment.json).

The verifier came from protected revision `c4bc7448b7a58a6affc4606dbbf7a138a1789f54`.
[Three time budgets](budget-only.patch) were extended: six hours overall,
two hours per module and two hours for the final checker stage. Acceptance
rules, sandboxing, axioms and pinned tools stayed at that revision.

The [original hosted attempt](https://github.com/GTimG/QuasiRiemannTracker/actions/runs/39027427377)
timed out compiling `Candidate.Cycle63.Optimization.MarkedSplit`.
The local source build passed that module and all 912 other submission modules.
The initial final-checker run exhausted its 25.5 GiB memory cap in con-ron.
[The retry driver](resume-judge.py) reauthenticated the hash-frozen source/build/export
checkpoint, repeated sandbox and checker controls, and reran Comparator plus all
three kernels with `con-ron --jobs=1`. The retry received a 29 GiB final-checker memory allowance within the 32 GiB VM;
see [the resource adjustment](retry-memory-adjustment.json).
Its accepted result is recorded here.
[Initial run](initial-replay.log), [retry](retry.log) and
[checkpoint](source-export-checkpoint.json) preserve that sequence.

[logs.json](logs.json) preserves exact UTF-8 log contents matching the receipt's
artifact hashes. All receipt artifacts were checked after authenticated SSH
retrieval. Large proof exports and library inventories remain in the operator's
evidence store, with their hashes in the receipt. Compiler/exporter bootstrap
trust remains a limitation. [Challenge.lean](Challenge.lean) is a statement
template; proof acceptance applies to [Solution.lean](Solution.lean).
