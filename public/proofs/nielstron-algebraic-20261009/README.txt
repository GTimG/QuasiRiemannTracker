# Nielstron: compressed proof at the exact algebraic endpoint

The exact threshold is 11/12-e/4, where e is the unique real root in
[1/6,1/5] of 657e^3-954e^2+21e+20=0. The same all-Dirichlet, zeta and
finite-order Eisenstein Hecke nonvanishing statements hold above it.
The independently stated rational corollaries use the upper bound
874957019420098946128603850561452983/1000000000000000000000000000000000000. Seven checked statements include unique root existence, so
the exact root hypotheses are not vacuous.

Native Lean verification passed at 2026-10-09T19:22:58.033625+00:00.
This immutable source collection retains status verification-pending:
independent Comparator/Lean/NanoDa/con-ron acceptance, if obtained later,
belongs in a separate dossier bound to this source manifest and public commit.
This snapshot alone does not claim external checker acceptance or a signed receipt.

The full native build covered 7233 modules, with
3132 locally built and 4101
official cache modules. The original seven protected files remain unchanged.
The native audit also checks all previous literal N24 targets by monotonicity.
Allowed axioms are only propext, Classical.choice and Quot.sound.

This continues the sequence: compression, rational certificate refinement,
then removal of approximation slack at the cubic endpoint. It does not
establish a new moment estimate or a threshold below the method's cubic barrier.
Nielstron is the human contributor; research and formalization were AI-assisted.
The work builds on Tim Gehrunger / ProofCouncil and OpenAI/math.

The exact pinned LeanLeanBench metric counts 259073 QRH tokens,
versus 251464 at the previous N24 result and 294019 in the immutable original.
Per-file counts, source hashes, and the separate unchanged OAI support scope
are in compressed/audit/token-counts.json. This is not an official benchmark
entry. Verification wrappers are separate audit artifacts outside that package.

## Reproduction

Run from this snapshot's root on Linux with Python 3, Git, tar and zstd:

```sh
python3 tools/setup_workspace.py --with-dependencies
python3 tools/reproduce_algebraic.py --output replay --compare-formalization compressed/formalization
python3 compressed/scripts/build_cached.py QRH QRH.Analytic QRH.Detector.UniformDetectorCount QRH.Hecke.DynamicBatchCount --jobs 16
python3 verification/verify_snapshot.py
python3 tools/count_lean_tokens.py
```

The source replay reconstructs the earlier compressed N24 proof from the
pinned public baseline, then applies the guarded algebraic source patch.
It compares every final source/configuration byte with the published snapshot.
The subsequent build and target audit are distinct from source replay.
These commands fetch pinned public dependencies and require no private Git
history. The source-inputs.json file identifies every source/configuration
byte. Compiler objects and toolchains are regenerated.

The inherited manuscript describes the earlier rational proof; the new root
construction and exact endpoint certificate are in QRH/AlgebraicRoot.lean and
QRH/Certificate.lean. The seven independent statements and target connections
are retained in verification/src. Original notices are retained in LICENSE,
UPSTREAM-NOTICE and compressed/third-party-notices.
