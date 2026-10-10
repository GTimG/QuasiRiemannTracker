# Single compensating prime: independent 29/33 analytic route

This is a non-record formalization and reusable-estimate contribution.
The precise source is under `formalization/`; the supplied paper is under
`manuscript/`. Start with `Verification.md` for the mathematical coverage.

The key endpoints are:

- `ZetaZeroFree.Analytic.beta_le_twenty_nine_thirty_thirds`;
- `ZetaZeroFree.Analytic.dirichletL_ne_zero_of_twenty_nine_thirty_thirds_lt_re`;
- `ZetaZeroFree.Analytic.riemannZeta_ne_zero_of_twenty_nine_thirty_thirds_lt_re`;
- `ZetaZeroFree.Analytic.heckeL_ne_zero_of_twenty_nine_thirty_thirds_lt_re`;
- `ZetaZeroFree.Analytic.Moments.D3.mixed_plain_moment_radical`.

The contributor's completed ordinary Lean 4.34.1 checks establish the stated
theorems using standard axioms only, independently of the previous terminal
7/8 theorem. The four main proof closures also passed local Comparator, Lean,
NanoDa and con-ron checks on 2026-10-10. The evidence is included for maintainer
review; no registry admission or signed receipt is claimed. See `NOTICE.md`
for provenance and publication rights.

From `formalization/`, with Python 3.9+, Git and elan installed:

```sh
python3 bootstrap_dependencies.py --check-bundle
elan toolchain install leanprover/lean4:v4.34.1
python3 bootstrap_dependencies.py --prepare
elan run leanprover/lean4:v4.34.1 lake exe cache get
python3 verify_analytic.py
```

The cache command is optional; the verifier builds explicit required targets.
Keep `lake-manifest.json` unchanged; do not run a floating dependency update.
The full OpenAI repository and local caches are unnecessary: its required
source closure is vendored as ordinary files. No GPU or FrankenLean is needed.

`evidence/analytic-verification-report.json` is a path-sanitized copy of the
completed source build, all-declaration dependency audit and fresh kernel
replay. `publication-transformations.json` records the original hashes.
`evidence/final-audit.lean` preserves the generated audit source. Negative
controls and their logs are in `evidence/negative-controls/`.

Historical earlier attempts mentioned in `Verification.md` are provenance,
not required inputs; this snapshot intentionally includes the final proof and
its current evidence. It excludes tracker state, old terminal-conclusion
wrappers, experimental proof loaders, caches and compiled `.olean` files.

## Manuscript formats

[Rendered PDF](../../public/proofs/single-prime-29-33-20261010/zeta_zero_free_4_33_self_contained.pdf) · [LaTeX source](manuscript/zeta_zero_free_4_33_self_contained.tex) · [Markdown source](manuscript/zeta_zero_free_4_33_self_contained.md)

The manuscript is by **Hailey Collet**, developed with assistance from OpenAI's
GPT-6 Pro. The publication revision adds author and contact details; the
mathematical text is unchanged. Original and revised hashes are recorded in
`manuscript/rendered-documents.json`. The PDF is published separately from the
UTF-8 source archive.
