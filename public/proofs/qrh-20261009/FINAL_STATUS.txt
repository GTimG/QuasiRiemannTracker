# Exact requested nonvanishing targets — PASS

Project: `/work/qrh-proof`, Linux verification worker.

`formalization/QRH/Nonvanishing.lean` proves and `QRH` exports:

- `QRH.DirichletCharacter.LFunction_ne_zero_of_theta_lt_re`
- `QRH.riemannZeta_ne_zero_of_theta_lt_re`
- `QRH.Hecke.LFunction_ne_zero_of_theta_lt_re`

The threshold unfolds to `(874957019421 / 1000000000000 : ℝ)`. Dirichlet quantifies over every `{q : ℕ} [NeZero q]`, every complex character and every complex argument in the strict half-plane, with exactly `¬ (χ = 1 ∧ s = 1)`. Hecke quantifies over the original finite-order Eisenstein character family over `CyclotomicField 3 ℚ`, with `s ≠ 1 ∨ χ.residue ≠ 1`. No primitivity or bounded-height restriction appears. Zeta includes the original Mathlib total-function value at 1, `(γ - log (4π))/2`, separately from the classical meromorphic pole.

## Verification evidence

`python3 scripts/build_source.py QRH QRH.Analytic --jobs 6` passed **7227/7227**, no failed or blocked modules, 13.574 s for the final integration replay. Six one-thread workers; matching locally source-built dependencies reused. The required original successor slice had independently built **6330/6330** in 1405.082 s; all later additions were compiled from source. No downloaded mathematical oleans were used. New target proofs were compiled from source, and the final audit checked all 7,227 source hashes, recursive dependency keys and matching compiler command/source records. This is not a claim that all dependencies were recompiled in an empty cache during the final 13.574 s.

`python3 scripts/verify_final.py` passed. The unchanged independent literal specifications, frozen before implementing the analytic extension, accept the actual three theorem constants in `audit/FinalTargetsRequired.lean`. The final compiler output in `logs/final-targets-required.log` is:

```text
'QRH.DirichletCharacter.LFunction_ne_zero_of_theta_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'QRH.riemannZeta_ne_zero_of_theta_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'QRH.Hecke.LFunction_ne_zero_of_theta_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There are no unproved analytic assumptions, `sorryAx`, native-evaluation axioms or other mathematical axioms in these transitive dependencies. Exact elaborated final types and original Hecke structures/functions are printed in `logs/final-declaration-types.log`. `audit/final-verification.json` is the machine-readable result, with source and specification fingerprints. Source provenance is in `audit/source-reverification.json`: eight immutable input checksums, three frozen targets, thirteen repository pins/notices, all selected source hashes, four original definition Git blobs, no conflicting selected license headers. Original OpenAI/math and mathlib tracked sources still equal their pins.

The proof uses 201 local modules, including 188 separately promoted analytic increments with 480 declaration-level axiom checks. It proves the needed actual extended masked moment, detector, optimized low/high probe, uniform saving, principal identification, analytic continuation, unconditional supremum bound and original all-character transfer. `audit/DEPENDENCY_MAP.md` describes these links.

## Exact environment

- Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Lean release archive SHA256 `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`; extracted executable SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- OpenAI/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Rellich–Kondrachov `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`.
- PrimeNumberTheoremAnd `c39a751132c88b6e8080b74c74023fd95b3d8be0`; four selected modules, with recorded OpenAI compatibility patches.

Every remaining exact package pin, license and retained notice is in `dependency-licenses.json`; patch source/hashes are in `applied-patches.json`. Selected reused mathematics is Apache-2.0. Argonaut is inspected but not imported, Liu code is not reused, Cli and non-Apache browser assets are outside the selected proof closure. See `LICENSES.md` and `local-source-attribution.json`.

## Scope and reproducibility

No proof obligation remains for the three requested final statements. The prompt allows the shortest sound analytic route: this development does not separately state every broader presentation of manuscript `lem:plain` (finite character combinations, zero-length absorption, all row presentations, β<51/100), or optional restricted optimality. The necessary specialization is proved and applied under β>θ, which discharges β≥51/100. None of those omitted standalone formulations is an assumption of the final theorems.

Fresh-workspace reconstruction and commands are documented in `../README.md`. Preserve the input snapshot separately and reconstruct the pinned compiler/dependencies with the reviewed bootstrap; use an initially empty task-owned `build/source` for an empty-cache rebuild. The convenience bootstrap has not been replayed end to end in a second empty workspace; its component acquisition/patch operations and the source builds have been performed here. The archive checksum is retained even though the downloaded compiler archive was removed earlier to recover task-owned disk space; the extracted compiler remains pinned and its executable hash rechecks.

Publication note: the historical verification results are retained with sanitized environment metadata. Operational checkpoint and session instructions are not distributed. See `../PUBLICATION.md`.
