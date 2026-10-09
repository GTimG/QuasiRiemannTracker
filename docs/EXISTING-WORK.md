# Existing formalized claims — selection review

Inspected 9 October 2026. These entries are candidates for the user to select; this document does not admit them to the verified registry. Source declarations, authors' verification reports and QRH Bounds verification are distinct. No external repository code was executed. The inspection hashes are in `evidence/existing-work-inspection.json`.

| Candidate              | Exact boundary                       | All-Dirichlet public entry                                             | Source revision                            |
| ---------------------- | ------------------------------------ | ---------------------------------------------------------------------- | ------------------------------------------ |
| OpenAI baseline        | 7/8 = 0.875                          | `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`      | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` |
| Argonaut Math          | 3499999/4000000 = 0.87499975         | `OAI.DirichletCharacter.LFunction_ne_zero_of_perturbed_boundary_lt_re` | `5971383edcb0b1cf863927eed3b359d2d3ba346e` |
| Baiying Liu, rational  | 34999/40000 = 0.874975               | `RHZeroFreeExtension.dirichlet_nonzero`                                | `7d10420de90efa2f082a06a342fc7accbd57ab37` |
| Baiying Liu, algebraic | (1507 − 2√921)/1653 ≈ 0.874957069799 | `RHV2.dirichlet_nonzero`                                               | `7d10420de90efa2f082a06a342fc7accbd57ab37` |

The inspected declarations cover all positive moduli and all complex Dirichlet characters with the same principal-pole exclusion. Liu expresses positivity by an explicit `q ≠ 0` and a local `NeZero` instance; a thin wrapper would adapt this to the canonical challenge. These are observations of source text, not a substitute for Comparator's definition, axiom and kernel checks.

## OpenAI

[Pinned proof](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean). The original proof has now been built on Linux verification worker and accepted by Palomar’s local Comparator, Lean, NanoDa and con-ron checks. See `public/proofs/palomar-20261009/openai/` for the report and transcript. This is separate from the uncommissioned signed admission service. Upstream license: Apache-2.0. The challenge template's `sorry` is never the proof.

## Argonaut Math

[Pinned terminal proof](https://github.com/Argonaut-Math/argonaut-math-quasi-riemann-boundary/blob/5971383edcb0b1cf863927eed3b359d2d3ba346e/lean/PerturbedBoundaryMain.lean), [build instructions](https://github.com/Argonaut-Math/argonaut-math-quasi-riemann-boundary/blob/5971383edcb0b1cf863927eed3b359d2d3ba346e/lean/BUILD.md), [Comparator workflow](https://github.com/Argonaut-Math/argonaut-math-quasi-riemann-boundary/blob/5971383edcb0b1cf863927eed3b359d2d3ba346e/.github/workflows/comparator.yml).

The repository reports Lean 4.34.1 and native Comparator success. Its checked-in workflow explicitly sets `enable_nanoda` to `false`, so that report does not meet this project's two-kernel policy. The full proof requires a release source package and reconstruction; the displayed terminal file alone is insufficient. The build instructions say that a fresh recipient rebuild has not yet been recorded. Repository license: Apache-2.0, with separate upstream notices. Its pins identify OpenAI commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; importing the overlay would require reviewed dependency/source integration, not changing our trusted challenge.

## Baiying Liu

[Rational entry](https://github.com/liubaiying101/Slightly-improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis/blob/7d10420de90efa2f082a06a342fc7accbd57ab37/RHZeroFreeExtension.lean), [algebraic entry](https://github.com/liubaiying101/Slightly-improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis/blob/7d10420de90efa2f082a06a342fc7accbd57ab37/V2FullVerification.lean), [explicit constant correspondence](https://github.com/liubaiying101/Slightly-improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis/blob/7d10420de90efa2f082a06a342fc7accbd57ab37/CombinedPaperVerification.lean), [verification script](https://github.com/liubaiying101/Slightly-improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis/blob/7d10420de90efa2f082a06a342fc7accbd57ab37/verify.py), [paper v1](https://arxiv.org/html/2610.12234v1).

The repository supplies Lean 4.34.1 declarations for both bounds. Its script attempts a Lean `--trust=0` replay and an axiom audit; it does not invoke Comparator or NanoDa. The pinned tree places `CombinedPaperVerification.lean` at its root, whereas the script expects `RHZeroFreeExtension/CombinedPaperVerification.lean`. The script also expects `vendor/LICENSE`, absent from that tree. These are concrete source-layout prerequisites to resolve before a reproducible build, not a mathematical rejection. No standalone contribution license was found in the complete pinned repository tree; link and attribute the work without vendoring its proof until licensing is clarified.

The algebraic constant is displayed in the catalogue with its exact expression and a certified rational enclosure used only for rendering; independent verification is pending. The separate signed admission contract remains rational-only. A separately proved rational corollary above the algebraic number could be submitted to that pipeline; no rounded decimal is silently substituted as its theorem constant.

## Other references

The [tomoto0 recheck repository](https://github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification) reports a rebuild of OpenAI's same 7/8 theorem. It is verification-related context, not a new numerical improvement. No comprehensive census is claimed by this initial review.
