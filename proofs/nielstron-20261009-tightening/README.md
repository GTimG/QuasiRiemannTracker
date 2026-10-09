# Nielstron: compressed proof and tighter rational bound

This AI-assisted contribution first compresses the ProofCouncil development,
then uses its exact rational certificates to prove all three original target
families at the smaller boundary

```text
874957019420098946128604623 / 1000000000000000000000000000
```

The improvement over `874957019421 / 1000000000000` is exactly
`901053871395377 / 1000000000000000000000000000` (about 9.01 × 10⁻¹³).
This is a modest refinement of the inherited argument, not a claim of the
Riemann hypothesis or a new analytic method.

**Catalogue status: verification pending.** The complete native Lean 4.34.1
build passed on 2026-10-09, checking all 7,232 modules in the selected closure,
including 206 QRH modules. The source build compiled 3,131 modules locally and
reused 4,101 official Mathlib cache modules. Three independently stated literal
rational targets, the original three targets, the strict improvement, and the
public zero-bound equivalences all passed. The only recorded axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

Comparator, NanoDa, and con-ron have **not** checked this candidate. The pinned
checker tools were prepared, but the genuine sandbox preflight failed before
executing proof code. No sandbox checks were bypassed and no signed admission
receipt was produced. See `tightening/checker-evidence/` and the explicit
external-checker field in `compressed/audit/tightening-verification.json`.

## Exact scope and source

`compressed/formalization/QRH/TighterNonvanishing.lean` exports nonvanishing
for all Dirichlet characters, the Riemann zeta function, and the same
finite-order Eisenstein Hecke family and exceptional pole condition as the
inherited proof. The independent specifications are in
`compressed/audit/TightIndependentTargets.lean`; they compile without QRH
imports. `TightTargetsRequired.lean` connects the new theorems to those literal
specifications. The original `QRH.theta` and original target source files are
preserved. The new rational is `QRH.tightTheta`.

The source baseline is the public tracker commit
`290d9c5463344c3e2fab93b878f3281e77e3fd6f`, under
`proofs/qrh-20261009/formalization`. Dependencies retain their pinned versions.
The new result builds directly on Tim Gehrunger / ProofCouncil and OpenAI/math.
Nielstron is the human contributor; compression, certificate refinement, and
formalization were AI-assisted. Retained source headers, `LICENSE`,
`UPSTREAM-NOTICE`, and `compressed/license/` document upstream attribution.

## Compression before tightening

The unchanged pinned LeanLeanBench tokenizer counts the QRH package as follows:

| Stage | Lean source tokens |
| --- | ---: |
| Immutable original | 294,019 |
| Compressed, original bound | 251,528 |
| Final compressed and tighter result | 251,464 |

The final reduction is 42,555 tokens (14.4736%). It includes shorter proofs,
shared binders, removal of unused helper declarations, readable public
corollaries, and the stronger result. These are source tokens, not LLM tokens.
Comments, imports, `lakefile.lean`, and `.lake` are excluded by the benchmark.
The unchanged selected OAI supporting source contributes 5,809,761 tokens:
QRH plus that fixed support decreases from 6,103,780 to 6,061,225 tokens,
about 0.6972%. Mathlib, Lean, and other fixed dependencies are outside both
reported source scopes. Per-file counts and hashes are in
`compressed/audit/token-counts.json`.

## Reproduction

Run from this snapshot's root on Linux with Python 3, Git, tar, and zstd.
Setup downloads the exact pinned public sources, Lean compiler, and official
Mathlib cache. No private repository or private Git history is required.

```sh
python3 tools/setup_workspace.py --with-dependencies
python3 tools/reproduce_tightened.py --output replay --compare-formalization compressed/formalization
python3 compressed/scripts/build_cached.py QRH QRH.Analytic QRH.Detector.UniformDetectorCount QRH.Hecke.DynamicBatchCount --jobs 16
python3 compressed/scripts/verify_tightening.py --numerator 874957019420098946128604623 --denominator 1000000000000000000000000000
python3 tools/count_lean_tokens.py
```

The first replay reconstructs the compressed proof from the immutable public
baseline, applies the rational tightening, and checks every final source byte.
The recorded replay matches all 210 source/configuration files. Source replay
alone is not proof verification; the subsequent build and target gates are
required. Compiler objects and local build logs are regenerated rather than
shipped. The archived native reports describe the completed author-side run.
The external checker suite remains a separate required step before upgrading
the catalogue status.

`compression-result.json` and `tightening-result.json` describe the final
251,464-token candidate. `tightening/baseline/` retains the historical
251,528-token compression-stage reports.
`publication-transformations.json` identifies neutralized workspace paths in
runtime metadata. Mathematical source bytes and gate outcomes are unchanged.
The repository manifest and public archive checksum authenticate the published
snapshot. Historical source-preparation reports may say that they had not yet
been Lean verified; the final target report records the later completed check.
