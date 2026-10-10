# A numerical slack retuning for review

This draft records an endpoint candidate, not an established stronger strip. Its complete retuned source is prepared and manual branch contracts have been reviewed; full proof verification remains pending. The exact rational candidate is

\[
\theta=\frac{437478509710049473064301925667}
 {500000000000000000000000000000}
 =0.874957019420098946128603851334.
\]

It is below the pinned historical Nielstron N24 value by exactly
`385833/500000000000000000000000000000`, or `7.71666e-25`.
The improvement recovers numerical slack in the existing argument;
it adds no new arithmetic estimate.

**Current-record clarification (10 October):** Nielstron's exact cubic
endpoint is now listed as framework-verified. It is stronger than this
rational proposal, which therefore does not improve the current record.
See the [pinned current catalogue](https://github.com/GTimG/QuasiRiemannTracker/blob/c4806753858945a008a92c564130809548e8c4bb/catalogue/results.json).

## Evidence supplied

- [PROOF_NOTE.md](PROOF_NOTE.md): a manual retuning argument relative to
  explicitly pinned proved analytic inputs, including the original
  character families, masks, principal poles and full recovery costs.
- [certificate.py](certificate.py) and [certificate.json](certificate.json):
  exact rational continuous endpoint and loss-budget checks.
- [PROVENANCE.json](PROVENANCE.json): attribution, source pins and scope.
- [SOURCE_REVIEW.md](SOURCE_REVIEW.md): new-instance branch gates, fresh
  source exclusions and the remaining verification obligations.

With Python 3.10 or later, run from this directory:

```sh
python3 certificate.py --check
```

The certificate checks the full endpoint rectangle with a square
identity and two Bernstein patches. It also checks the replacement
recovery budgets and rejects keeping the previous fixed budgets.
It does **not** establish the analytic inequalities.
Its 34 exact checks include the low physical-scale and principal
contour conditions found during the source review.

## Source re-instantiation

[source_retuning.patch](source_retuning.patch) contains 13 changes against
the pinned compressed formalization. It is intended for a **new copy**
of the entire source cohort, not for modifying immutable published
snapshots. All 205 existing QRH modules must be re-instantiated and
validated; frozen low/count/principal/transport APIs cannot be invoked
at the new geometry merely because the parameter difference is tiny.

The [source preparer](prepare_sources.py) validates every baseline
source/configuration byte, copies the entire cohort to a new build
directory, and reproduces the patch and candidate hashes. It never invokes
Lean. From the tracker checkout root, run:

```sh
python3 docs/proposals/gao-slack-retuning-20261009/prepare_sources.py
```

The two copied upstream coefficient generators in `inputs/scripts/`
retain their upstream Apache-2.0 terms and notices. The public baseline's
`proof_length.py` token-count helper is neither copied nor executed.

[Source metadata](source_retuning.json) and the
[rebuild inventory](dependency_rebuild_inventory.json) record this scope.
[Independent targets](IndependentSlackTargets.lean) and the
[target/axiom gate](TargetAndAxiomGate.lean) are uncompiled validation
inputs. The original L-functions, character scope and pole exceptions
are retained. No stronger-strip premise is added.

The exact source baseline is
`proofs/nielstron-20261009-tightening/compressed/formalization`
at tracker commit `40844a7614b67840801e65b836b3da2e1f7ff029`.
The patch paths are relative to a copied cohort's parent directory.
Verify the input and output hashes, then rebuild the whole cohort with
the upstream pinned dependency environment; do not reuse old QRH
compiled libraries as evidence for changed geometry.

The patch includes Apache-2.0 upstream-derived source changes; their
[license](UPSTREAM_LICENSE) and [notices](UPSTREAM_NOTICE) are retained.
The local MIT license covers the new author note/certificate, not a
relicensing of that upstream material.

## Review status

An uncompiled full-source retuning patch and independent literal target
specifications are supplied. No Lean compilation, Comparator check,
NanoDa check or con-ron check has been performed. The note has internal model-assisted review of the
retuning and assembly contracts, without a new independent audit of
every upstream analytic proof. It retains the mathematical validity
of those named inputs as a condition.

This is an evidence-only proposal for maintainer review. It requests
neither a catalogue entry nor a verified badge, and therefore does
not move the chart or signed registry. A qualifying unconditional
all-character submission and its required checking evidence remain
separate work.

The contribution is by Zhongpai Gao, with AI assistance. Its analytic
architecture and existing formalization are credited to OpenAI,
Tim Gehrunger / ProofCouncil and Nielstron. The new note and certificate
are provided under the included MIT license; referenced upstream work
retains its original terms.
