# A local moment refinement near the quartic zero-free boundary

Zhongpai Gao, with AI assistance. 11 October 2026.

Read the [8-page main paper](https://github.com/Gaozhongpai/QuasiRiemannTracker/blob/gao-local-moment-source-review-20261011/public/proofs/gao-local-moment-20261011-paper/paper.pdf) or the
[39-page analytic supplement](https://github.com/Gaozhongpai/QuasiRiemannTracker/blob/gao-local-moment-source-review-20261011/public/proofs/gao-local-moment-20261011-paper/supplement.pdf).
The main paper explains the theorem, the two-part moment argument, and the
exact endpoint. The supplement contains the detailed derivations in sections
A–I. The proposed boundary is `4374433/5000000 = 0.8748866`, relative to the
pinned Cycle25/OpenAI/Levy framework cited in both documents.

This is an editorial reorganization. All eight technical proof sections are
preserved byte-for-byte from the earlier source snapshot, as recorded in
[content-preservation.json](content-preservation.json). The earlier manuscript,
compiled components, audit results, and evidence retain their original files.

## Verification scope

The [supporting evidence](../gao-local-moment-20261011-v3/README.md) records
15 compiled Lean components and 48 named axiom checks using only standard
axioms, with cached imported dependencies. These checks cover supporting
results. Complete formalization of the all-family endpoint, clean dependency
replay, Comparator verification, and the required kernel checks remain pending.
No verified leaderboard status is claimed by this manuscript package.

## Build and reproduce

With Tectonic installed, run these commands in this source directory:

```sh
tectonic paper.tex
tectonic supplement.tex
python3 endpoint_extra_arithmetic.py --check
```

Keep the generated PDFs together so the relative link from the main paper to
the supplement works. The supplement also identifies each technical section
by its printed letter. The existing exact arithmetic checks and component
replay instructions are linked from the supporting-evidence README above.

Source pins, mathematical attribution, and the Apache-2.0 license notices are
retained. The author acknowledges the upstream work of OpenAI, Hailey Collet,
and Akash Levy, and AI assistance in research, computation, formalization, and
exposition.
