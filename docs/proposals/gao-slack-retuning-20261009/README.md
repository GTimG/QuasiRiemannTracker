# A numerical slack retuning for review

This draft proposes the exact rational

\[
\theta=\frac{437478509710049473064301925667}
 {500000000000000000000000000000}
 =0.874957019420098946128603851334.
\]

It is below the catalogue's Nielstron value by exactly
`385833/500000000000000000000000000000`, or `7.71666e-25`.
The improvement recovers numerical slack in the existing argument;
it adds no new arithmetic estimate.

## Evidence supplied

- [PROOF_NOTE.md](PROOF_NOTE.md): a manual retuning argument relative to
  explicitly pinned proved analytic inputs, including the original
  character families, masks, principal poles and full recovery costs.
- [certificate.py](certificate.py) and [certificate.json](certificate.json):
  exact rational continuous endpoint and loss-budget checks.
- [PROVENANCE.json](PROVENANCE.json): attribution, source pins and scope.

With Python 3.10 or later, run from this directory:

```sh
python3 certificate.py --check
```

The certificate checks the full endpoint rectangle with a square
identity and two Bernstein patches. It also checks the replacement
recovery budgets and rejects keeping the previous fixed budgets.
It does **not** establish the analytic inequalities.

## Review status

No modified Lean development, Comparator check, NanoDa check or con-ron
check is supplied. The note has internal model-assisted review of the
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
