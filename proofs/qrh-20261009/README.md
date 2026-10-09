# Exact QRH nonvanishing — three final targets checked

The requested all-Dirichlet, zeta and finite-order Hecke nonvanishing theorems are proved at exactly `(874957019421 / 1000000000000 : ℝ)` in `formalization/QRH/Nonvanishing.lean`, exported by `QRH`. The all-character scope, positive-modulus instance, original L-functions and principal pole exceptions match the frozen independent specifications. Each final theorem has only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.

Workspace: `/work/qrh-proof`, Linux verification worker. The final source build passed **7,227/7,227 modules**, with six Lean workers of one thread each. `audit/final-verification.json` records the independent statement/axiom gate and the recheck of every source/dependency key and matching compiler log. `audit/FINAL_STATUS.md` contains the precise scope, pins and handoff details; `audit/DEPENDENCY_MAP.md` explains the analytic proof.

```sh
python3 scripts/build_source.py QRH QRH.Analytic --jobs 6
python3 scripts/verify_final.py
```

This is the documented build route. It compiles the selected mathematical and tactic dependencies from pinned source, using only the compiler's standard library as a precompiled baseline. It never downloads mathematical oleans. Matching outputs from the already reproduced upstream slice are reused only under exact source/dependency keys. The new final proof targets were compiled from source; all 7,227 keys and corresponding compiler command/source logs were subsequently checked. The last integration replay is not described as a second empty-cache build of all dependencies.

For a clean reconstruction in a **new authorized isolated workspace**, preserve the source/audit files and immutable input snapshot, inspect and run `python3 scripts/bootstrap.py`, then the two commands above with an initially empty `build/source`. The bootstrap pins compiler archives and repositories and applies only the recorded compatibility patches. It never launches Codex or accesses credentials. The convenience bootstrap has not been replayed end to end in a second empty workspace; its individual operations and the selected source builds were performed and logged here. Do not remove another job's outputs. `formalization/lakefile.lean` describes the corresponding local libraries; the bounded custom builder is the verified route.

Pins: Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`), OpenAI/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. All transitive source pins/notices are in `audit/dependency-licenses.json`; compatibility patches are in `audit/applied-patches.json`. License scope, unused non-Apache assets and local adaptations are documented in `audit/LICENSES.md` and `audit/local-source-attribution.json`.

The analytic argument extends the actual masked moment through the coefficient transport and width induction, constructs the same optimized physical probe for low and high bounds, proves a uniform saving, and applies Mellin continuation to the actual Hecke zero supremum. No analytic contract is assumed by the final theorems. Intermediate conditional statements have their premises discharged in the final dependency chain. This follows the prompt's shortest-route allowance: it does not separately package every presentation of manuscript Lemma `lem:plain`, nor prove optional restricted optimality. These omissions are not premises or unresolved obligations of the three final theorems.

Zeta at 1 follows Mathlib's nonzero total-function value `(γ - log (4π))/2`, distinct from the classical meromorphic pole. The explicit Dirichlet and Hecke pole exceptions are preserved.

The retained input fingerprints, accepted manuscript SHA256 `c8b9994d6a55521b53fe4664ba190e46dc0a02f7d85221e25d39efa4dcd34de9`, three frozen target hashes, original definition Git blobs and selected Apache source provenance all recheck. Inputs and original OpenAI/math and mathlib sources are unchanged. Old partial/failing reports are historical; use `audit/final-verification.json` for current status. `scripts/verify_partial.py` intentionally remains a historical partial-check utility, not the final completion checker.


Publication note: operational handoffs and session records are omitted. Logs and environment metadata use neutral paths and worker labels; see `PUBLICATION.md`. Mathematical sources, targets, manuscript and dependency pins are unchanged.
