# Independent verification of PR #73

The exact source `41ddc0ddea6b4de6829d8cc1f94afa4e22c748f3` passed at 2026-10-25T20:44:20.989546+00:00 for the all-Dirichlet
bound `8747289/10000000` (0.8747289). The only theorem change from the pinned
OpenAI statement is its rational constant. All positive moduli, complex Dirichlet
characters, complex arguments, the original pole exclusion and L-function remain.
The intentional `sorry` in [Challenge.lean](Challenge.lean) is a statement template,
never the accepted proof.

The original outside-sandbox [receipt](result.json), SHA-256
`957a5129edb1911dfcd1d692c25b576359d27077d89a1e69e63f788d2fb401a4`, binds the exact source, generated challenge,
submission/dependency trees, library inventory, tools and logs. It was retrieved
over authenticated SSH and validated against trusted preparation from immutable
Git objects. [judge.log](judge.log) records Comparator statement, transitive
definition and axiom comparison, and acceptance by Lean, NanoDa and con-ron.
Only `propext`, `Classical.choice` and `Quot.sound` were permitted.

## Checker and isolation

The check used pristine upstream NanoDa 0.4.26 at
[`998e0a84e4c1572ca279ff05007af6ec6639405a`](https://github.com/ammkrn/nanoda_lib/tree/998e0a84e4c1572ca279ff05007af6ec6639405a),
the version validated during PR #69's capacity investigation. Its exact source
manifest, original Apache-2.0 license and binary hash are included. All other
checker binaries retain the protected pins. This explicit local runtime upgrade
does not change the hosted workflow's pins. It does not use the earlier locally
patched diagnostic checker.

The upstream build passed 54 tests, with no failures and eight documentation tests
ignored upstream. Those authenticated build/test records were reused. This run
privately copied and authenticated the runtime and reran the real OpenAI 7/8
baseline through Comparator and all three kernels. Only the baseline/control
exports were reused from the previously authenticated baseline build; its kernel
checks were rerun here. [baseline-judge.log](baseline-judge.log) records acceptance.
Fresh confinement, positive proof, mismatched statement and ill-typed proof
controls passed; hidden assumptions and `sorryAx` were explicitly rejected.

All 6,763 required submission and OpenAI modules
compiled fresh. No candidate/OpenAI compiled cache was reused. Approved pinned
non-OAI dependencies were copied into a private library and hashed before and
after checking. The trusted challenge was exported before candidate execution
and its digest remained unchanged. The worker used Palomar's actual unprivileged
Linux sandbox, no network during checking, private writable scratch, read-only
inputs, no host credentials, and bounded CPU, memory and time. Receipts were
generated outside candidate-writable directories.

## Resources, provenance and limitations

The protected verifier revision is `5c8b17807e9d11f500d79de487fa38ace7265bfb`.
Palomar is pinned at `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`; source Lean is
4.34.1 and the Comparator runtime is 4.35.0-rc2 with the NanoDa replacement above.
The worker was capped at 256 GiB and 16 CPU threads. The protected replay driver
only received documented time-budget increases: shared 3h to 24h, final judge
1h to 16h, each module 30min to 2h, and exports 10min to 2h. See
[budget-only.patch](budget-only.patch) and [replay-driver.txt](replay-driver.txt).
No statement, axiom, sandbox or acceptance rule was weakened.

The initial hosted admission timed out during Comparator checking. This independent receipt relies
on the separately authenticated ETH run and its full retained logs. Compiler/exporter bootstrap and approved dependency
provenance remain part of the trust model; successful tests do not prove that
kernel implementations have no bugs. The complete exported proof is still
required to pass all three kernels.

## Reproduction and evidence

Use the exact source, dependency and checker pins. Prepare the challenge from the
protected generator and exact rational, reproduce confinement/rejection controls
and baseline acceptance, then freshly compile the approved source closure in the
real sandbox and run Comparator with all three kernels. To rebuild NanoDa, fetch
the locked dependencies separately, then use `cargo test --locked --offline` and
`cargo build --release --locked --offline` in a private build directory. Never
accept a candidate-provided challenge, runtime, cache or verification receipt.

[logs.json](logs.json) preserves compiler and checker logs with private filesystem
paths removed; [log-redactions.json](log-redactions.json) records original/public
hashes. The raw receipt is unmodified. Large frozen exports and full private
inventories remain on the verification worker and are bound by hashes.

ArviFoxy's authorship, Hailey Collet's predecessor contribution, the two-level
affine development, OpenAI's framework and inherited notices/licenses are retained. Verification, PR submission, merge and publication
times are distinct. Publication requires an exact-head registration and successful
authenticated protected admission in addition to this receipt.
