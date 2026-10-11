# Local physical moment: compiled source components

Eight source components support the proposed capacity 4.498 and conditional
endpoint 0.8748866. They do not prove the complete physical moment or endpoint.
The manual source argument belongs to
[the candidate](../../candidates/LOCAL_PHYSICAL_MOMENT_EXTENSION.md).

| Module | Proved scope |
|---|---|
| `FiniteDeletionBins` | Positive-half-plane zeros and buffered maxima survive the exact finite Euler mask. |
| `UnmarkedDensity` | Existing unmarked inverse/plain moment inputs imply the fiber density exponent, with explicit loss; its exponent exceeds one sixth. |
| `BufferedSlot` | The actual natural relative slot has the buffered pointwise bound, with its punctures and independent frequencies. |
| `RestrictedIncumbent` | Cheap slot removal on low rows feeds the existing remaining-state moment, with separate removal and incumbent costs. |
| `SixthRowMask` | The actual sixth-power frequency decomposition preserves precisely the original Euler holes and zero bins. |
| `RawSixthDensity` | A uniform free-row density bound implies the all-integer-row bound through a convergent ideal convolution. |
| `UniformDensity` | Eventual free-row estimates extend to bounded windows uniformly in the row predicate; one convolution constant works for all exponents above a fixed threshold. |
| `UnmarkedBatch` | The actual witness labels and two dyadic lengths partition the unmarked rows, without positive slot supply; witnesses need exist only on selected rows. |

The [axiom audit](formalization/LocalMoment/SourceAudit.lean) checks the named
declarations. [Compile evidence](evidence/component-replay.json) records fresh
compilation with the pinned Lean 4.34.1 executable against existing dependency
objects, including source and output hashes. All checked declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.

This is development verification. Imported dependencies were not rebuilt in
this run. Comparator, canonical all-family targets, and the three independent
kernels have not accepted the new candidate.

## Reproduction

Use the pinned OpenAI/Cycle25 dependency libraries described in the parent
candidate's provenance. This package contains local sources, not their cached
dependencies. Supply the exact compiler and every required library directory:

```sh
python3 replay_components.py --lean /path/to/lean-4.34.1/bin/lean \
  --library /path/to/mathlib/lib/lean --library /path/to/OAI/lib/lean \
  --library /path/to/other-dependencies/lib/lean --work-dir /new/empty/directory
```

Repeat `--library` as needed. The runner checks the compiler digest, copies only
the local `.lean` sources to the empty directory, compiles them in dependency
order, and checks every listed axiom set. It does not fetch or execute upstream
scripts. Existing OAI, Mathlib, and auxiliary dependency objects must match the
pinned compiler; the example paths are placeholders.

## Remaining source obligations

The unmarked moments and supported witnesses are explicit hypotheses. They
must still be supplied from incumbent physical moments and actual buffered
zero bins, with uniform conductor and height bounds. The exact label and
dyadic factors in `UnmarkedBatch` must be paid, not silently discarded.

The remaining physical proof also needs the signed-twist-to-integer-row map,
joint reconstruction of both common labels and the first projector, the
comparison-only mask reflection, fixed-amplifier terminal budgets retaining
negative margins, and full Fourier/height assembly. The endpoint certificates
remain conditional until those obligations and the canonical checks are met.

New component work: Zhongpai Gao, AI-assisted. The batch partition is adapted
from OpenAI's `DetectorBatch` and `DetectorFiberPartition`; upstream mathematical
and formal dependencies retain their original authorship and licenses.
