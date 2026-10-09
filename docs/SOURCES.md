# Inspected sources and pins

PalomarSubmission is MIT-licensed. Its copyright and license notice is retained in `public/proofs/palomar-20261009/PalomarSubmission-LICENSE.txt`. The checker may be used independently; our checks do not imply Palomar registration or endorsement.

The completed local Palomar checks use PalomarSubmission at
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` and the Comparator, Lean, NanoDa and
con-ron tools bundled with official Lean `v4.35.0-rc2`. Both proofs passed.
The proof compiler remains `v4.34.1`, with its matching exporter at
`076e8e57707e813375e8f9da8bf989799ace9680`. Full binary hashes, reports and scope
limitations are in `public/proofs/palomar-20261009/`. Its tool-pins files record
the preparation stage; the subsequent result and check-status files record acceptance.

## Separate signed-admission service

Source inspections and identifier resolution were performed on 2026-10-09. Full machine-readable pins are in `verifier/pins.json`, with the resolved Lean dependency graph in `worker/lake-manifest.json`. No checking job resolves a floating branch.

| Component                      | Pinned revision                            | Notes                                                                            |
| ------------------------------ | ------------------------------------------ | -------------------------------------------------------------------------------- |
| OpenAI math                    | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` | Apache-2.0; original license retained                                            |
| Comparator                     | `d03acab154d269c06e60e4de7e4cc85deebff94b` | Apache-2.0; 4.34 line, built here with 4.34.1                                    |
| lean4export                    | `076e8e57707e813375e8f9da8bf989799ace9680` | Comparator's resolved exporter; export format 3.1.0                              |
| NanoDa                         | `3a2407216ee84a75f9e1aead6803d0578be06ae7` | Apache-2.0; 0.4.19; parser accepts format >=3.1.0 and <3.2.0; execution untested |
| Landrun                        | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` | Frozen source, Go dependencies locked; runtime untested here                     |
| Mathlib                        | `d13f23b723b8a846827a245b89c10fc7d3f11612` | Same revision as the canonical challenge                                         |
| Visual/functionality reference | `d8e39034757365b948c8d7e0e18d859a26a98227` | No license grant found; no source/assets reused                                  |

Lean is fixed at `leanprover/lean4:v4.34.1`. Comparator's latest inspected HEAD (`ca04cfc72b550331658ec314bf47685281bfd4bf`) uses 4.35.0-rc4 and is intentionally not used. Comparator/exporter 4.34.0 sources compiled unmodified with the 4.34.1 toolchain (only the toolchain selectors were changed). This is build compatibility, not a completed kernel check. NanoDa format compatibility was inspected in source but still requires baseline execution.

[Canonical challenge](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/ComparatorChallenges/DirichletSevenEighths.lean) · [Baseline proof](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean) · [Comparator requirements](https://github.com/leanprover/comparator/tree/d03acab154d269c06e60e4de7e4cc85deebff94b) · [Reference implementation](https://github.com/Paureel/beyond-n-log-n/tree/d8e39034757365b948c8d7e0e18d859a26a98227) · [Reference website](https://beyond-n-log-n.netlify.app/)

The canonical upstream `sorry` is a deliberate statement hole. The generator preserves the theorem hypotheses/definitions and changes only its rational literal and declaration namespace/name. It is never submitted as an acceptable proof. No definition holes are permitted.

The worker's baseline closure includes 2,924 OAI modules with external roots Mathlib, PrimeNumberTheoremAnd and RellichKondrachov (plus Lean). Only this closure is copied. The exact upstream compatibility patches for the latter two libraries are applied during the trusted image build. The canonical `import Mathlib` still requires the pinned Mathlib umbrella; its approved prebuilt cache is part of the trusted image supply chain.
