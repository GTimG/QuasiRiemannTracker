# Local moment research revision 3

11 October 2026. Zhongpai Gao, with AI assistance in research, formalization,
computation, and exposition.

This revision supplies a full source-level analytic argument for review, from
the local moment modification to the proposed boundary
`4374433/5000000 = 0.8748866`. It relies on the pinned incumbent results
identified in the manuscript. It has not received independent mathematical
certification, a complete formal endpoint proof, or tracker acceptance.

Read the [PDF manuscript](https://github.com/Gaozhongpai/QuasiRiemannTracker/blob/gao-local-moment-source-review-20261011/public/proofs/gao-local-moment-20261011-v3/paper.pdf)
or [LaTeX source](paper.tex), beginning with its introduction and proof
roadmap. The supplementary sections give the exact arithmetic and analytic
steps behind the shorter main exposition. This is a new snapshot; revisions
1 and 2 retain their original contents and historical status.

The main additions are:

- The actual unmarked plain input, including the finite exceptional free
  cores, and a density argument with its threshold chosen before height.
- Signed row identities retaining natural zeros, both coprimality projectors,
  the fixed character dictionary, and the natural conductor bound.
- The exact low-row restriction, padded main radius, and combined correction
  for the actual child width and the slot-removal cost.
- Common Fourier transport, joint high-row counting, comparison terms,
  amplification errors, and centered exceptional cancellation.
- The endpoint application on shortened ordinary scales and short selected
  prime products, with the original amplitude gain preserved.

## Checked evidence

Fifteen Lean components and the audit module were freshly compiled from
source with the pinned Lean 4.34.1 executable. All 48 named axiom checks use
only `propext`, `Classical.choice`, and `Quot.sound`. Imported dependency
objects were reused. Two tactic-style warnings occur in `LowSourceAdapters`;
they do not affect compilation or the axiom checks.

The complete local-moment and all-family endpoint theorems are **not** among
these 48 checked declarations. In particular, the written density, Fourier,
and endpoint assemblies must not be represented as machine-verified by this
component report. The exact rational audits in revision 1 were rerun and
passed; their original conditional scope is unchanged. The additional
endpoint script checks 20 exact rational comparisons, including the far-row,
empty-product, principal-probe, and feedback bounds.

The six additional components are `HeightUniformDensity`,
`PlainUnmarkedAdapter`, `SignedRows`, `LowSourceAdapters`,
`RestrictedCanonicalSource`, and `ScaleShortening`. Their statements and
the complete list of audited declarations are in
[SourceAudit.lean](formalization/LocalMoment/SourceAudit.lean).

## Replay

Supply the compiler and pinned dependency libraries described in the earlier
snapshot, including the incumbent certified-base library, then run:

```sh
python3 replay_components.py --lean /path/to/lean-4.34.1/bin/lean \
  --library /path/to/certified-base/lib \
  --library /path/to/mathlib/lib/lean \
  --library /path/to/OAI/lib/lean \
  --library /path/to/other-dependencies/lib/lean \
  --work-dir /new/empty/directory
```

Repeat `--library` for each required package. The runner authenticates the
compiler, copies only these local sources, compiles them in dependency order,
and checks the printed axiom sets. It does not rebuild imported dependencies.
Public replay evidence replaces machine-specific library paths with labels;
the source, object, and log hashes are unchanged.

Build the manuscript with a current LaTeX installation or `tectonic paper.tex`
from this directory. Keep every companion `.tex` file beside `paper.tex`.

Run `python3 endpoint_extra_arithmetic.py --check` for the new endpoint
arithmetic. The original Bernstein and physical-ledger audits remain in the
first snapshot, `../gao-local-moment-20261011/research/tools/`.

## Submission status

This is a draft research contribution for source review. No verified-record
label, catalogue entry, independent Comparator receipt, or three-kernel
receipt is claimed. Maintainer review and independent verification remain
necessary before the proposed bound can be accepted as a verified result.
