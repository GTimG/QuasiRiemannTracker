# Local physical moment research candidate: 0.8748866

Prepared for Zhongpai Gao, 11 October 2026, with AI assistance.

The proposed local physical moment has capacity **4.498**. Its conditional
endpoint **4374433/5000000 = 0.8748866** lies strictly below the exact quartic
incumbent. The full local physical Lean adapter and canonical all-family
Comparator/three-kernel validation are pending. This upload is a research
candidate, not an accepted tracker record; no catalogue status is changed.

Start with [the candidate and its exact source obligations](research/framework/programs/fixed_strip/candidates/LOCAL_MOMENT_TRACKER_REFINEMENT.md),
then read [the manual local source argument](research/framework/programs/fixed_strip/candidates/LOCAL_PHYSICAL_MOMENT_EXTENSION.md).
The [squared-label lemma](research/framework/programs/fixed_strip/candidates/JOINT_HIGH_ZERO_SQUARED_LABEL_PAYMENT.md)
explains the joint population count.

The exact source audit includes 11 continuous interval certificates,
317,376 joint integer-fibre checks and 72 actual sextic CRT controls.
The conditional endpoint audit checks 18 upper-row rectangles, six incumbent
rectangles below the local window and the lower row endpoint. These tests
certify their finite/scalar statements, not the new analytic theorem.

For review scope and the remaining theorem obligations, see [REVIEW.md](REVIEW.md).

## Compiled source components

Eight [Lean source components](research/framework/programs/fixed_strip/verification/local_moment_source_2026-10-11/README.md) now compile
with the pinned Lean 4.34.1 executable. Twelve axiom checks report only the
standard axioms. This includes uniform small-window and exponent constants
and the unmarked witness partition. Imported dependencies were reused; the
full physical theorem and canonical checks remain pending. The source,
compile logs, hashes and a separate component replay script are included.

## Reproduce

Requires Python 3 and SymPy 1.14.0. The commands fetch only a pinned paper
when requested and never run Lean or upstream reproduction scripts.

```sh
python3 reproduce.py --fetch-pinned-paper
python3 research/tools/local_physical_moment_audit.py --check
python3 research/tools/local_moment_endpoint_audit.py --check
```

`SHA256SUMS.json` binds every uploaded research and metadata byte. The paper
is fetched from the exact Cycle25 source pin and its digest is checked against
the source audit. Upstream original authorship and Apache-2.0 notices are retained.
See [upstream notices](UPSTREAM_NOTICE.md), [source pin](upstream-source.json)
and [current acceptance state](STATUS.json).
