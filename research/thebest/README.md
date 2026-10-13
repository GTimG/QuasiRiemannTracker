# Structural research: escape the quartic envelope

First research pass by Thibaud Gloaguen's @thebest agent, with three research
sub-agents. Upstream: `d716ecaae80f7823a5b8314916364fdfa0d133fb`.
This directory is exploratory research, not a new-bound submission.

## Result: a geometry-only obstruction

The exact root and boundary in Collet's Cycle25 manuscript were reproduced
arithmetically: `b₀ ≈ 0.8748866470399641`. We have not replayed Lean,
Comparator or the independent kernels; Lean is not installed on this host.
The existing reviewed catalogue remains authoritative about prior verification.

Let `P(l)=927l⁴−3135l³+2433l²+275l−100`, `b(l)=11/12−l/4`,
`κ=(5−3l)/6`, and

```
δ(l) = κ(5−9l) / [6κ+(6κ+2)l].
p = 1/2.
```

Substitute these into the unchanged B0.47 scalar envelope, replacing `ell₀`
and `h₀` by `l` and any positive `h`. Exact symbolic algebra gives

```
F(l,h,δ(l),1/2) − b(l)
  = h (21l−40) P(l)
    / [24(3l²−4l−5)(234l³−753l²+525l+100)].
```

On `1/6 ≤ l ≤ 1/5`, the rational multiplier of `h P(l)` is strictly
positive. Also `0 < δ(l) < 5/6`, so this is an admissible scalar test point.
The quartic is strictly increasing on that interval (derivative at least
`3549/5`) and its unique root is `l₀`. Consequently every `l>l₀` in this
interval fails the scalar certificate for every `h>0`.

This rules out improving that certificate by optimizing `h`, choosing `h`
adaptively at the binding cell, or averaging its exponents with nonnegative
weights at a common `l`. Actual sums could be smaller than their upper bounds:
this is **not** an impossibility theorem for analytic improvements. Coherent
cancellation between probes, different `l` in a new combined argument, or
new moment estimates are outside the obstruction. Using B0.47 outside the
range where its analytic derivation applies would not establish a bound either.

## Structural direction

Instead of counting zero-witness rows and then applying a fourth moment to
the numerator, retain the witness and numerator in one mixed moment. The
companion `joint-*` files investigate the exact local saving needed and the
missing analytic input. The candidate is a research target, not an available
theorem. In particular, a gain for the short-witness cell must also survive
the long-witness branch, coefficient shifts, all amplitude cells, and common
uniformity requirements before it can imply a zero-free bound.

The local diagnostic identifies a required saving of about `0.00099705` in
the mixed-moment exponent over the pointwise reduction at the binding cell.
This is a target for a new analytic lemma, not an achieved saving.
`joint-moment.png` illustrates the conditional comparison.

The independent notes `audit.md` and `structural-ideas.md` describe additional
routes and why easy applications of existing estimates do not suffice.

## Reproduction

Use Python 3 and the package versions in `requirements.txt`:

```sh
python3 -m venv /tmp/qrh-research-venv
/tmp/qrh-research-venv/bin/pip install -r research/thebest/requirements.txt
/tmp/qrh-research-venv/bin/python research/thebest/barrier.py
/tmp/qrh-research-venv/bin/python research/thebest/joint-moment.py
```

`barrier-results.json` records exact identity and rational sign checks.
The decimal display uses numerical root finding only after the root interval
and uniqueness were checked separately. These checks establish the elementary
algebra in the note, not the analytic hypotheses or an independent kernel proof.

All research files are separate from the catalogue, existing proof snapshots,
and verification infrastructure. No result was submitted upstream.

## Attribution

The starting formulas and current quartic boundary are from Hailey Collet's
`proofs/cycle25-quartic-20261010/manuscript/paper.tex`, especially B0.38–B0.49,
which builds on OpenAI/math and Akash Levy's weighted numerator. The new
contribution here is the explicit obstruction identity and the exploration of
possible structural escapes. This local research is under the repository's
Apache-2.0 license; upstream notices are retained.
