This PR proposes a small numerical retuning of the pinned Nielstron boundary, with reproducible arithmetic and source-preparation evidence.

The proposed rational is
`437478509710049473064301925667 / 500000000000000000000000000000`
(`0.874957019420098946128603851334`). Its exact difference from the current reference is `7.71666e-25`. This recovers numerical slack in the existing argument; it introduces no new arithmetic estimate.

### What is included

- A standalone exact-rational certificate with **34 checks** covering the continuous endpoint rectangle, complete numerical recovery budget, and low/principal geometry conditions.
- A reproducible **13-file source overlay**, with pinned input hashes and manifests for the complete 210-file candidate cohort.
- Independent literal targets for all positive-modulus Dirichlet characters, zeta, and the original finite-order Eisenstein Hecke family, retaining the original L-functions and pole exceptions.
- A source-contract review, explicit remaining obligations, provenance, and upstream licenses.

### Reproduce

From the tracker checkout root:

```sh
python3 docs/proposals/gao-slack-retuning-20261009/certificate.py --check
python3 docs/proposals/gao-slack-retuning-20261009/prepare_sources.py
```

The baseline is tracker commit `40844a7614b67840801e65b836b3da2e1f7ff029`.

### Verification status

**The arithmetic checks pass; the complete stronger nonvanishing theorem is not yet verified.** The source overlay and target/axiom gate are uncompiled. Full-cohort elaboration, independent statement/definition/axiom comparison, and Lean/NanoDa/con-ron replay remain pending. The internal model-assisted source review does not independently validate every upstream analytic proof, and website/publication checks do not prove this theorem.

This proposal requests maintainer review, **not a catalogue entry or verified badge**. The existing analytic architecture and formalization are credited to OpenAI, Tim Gehrunger / ProofCouncil, and Nielstron.

See [the proposal README](https://github.com/Gaozhongpai/QuasiRiemannTracker/tree/gao-slack-retuning-20261009/docs/proposals/gao-slack-retuning-20261009) for the proof note, certificate, source patch, and detailed scope.
