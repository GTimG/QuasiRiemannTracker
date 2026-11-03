# Axiom Math general number-field submission (draft)

This package preserves the actual general-family proof imported from
[AxiomMath/DedekindZetaZeroFree](https://github.com/AxiomMath/DedekindZetaZeroFree/tree/09afbb4ce6570c1615d58509dc197fc9f0956b7d).
The source repository was created on 12 October 2026 at 18:06:30 UTC; the
imported revision is `09afbb4ce6570c1615d58509dc197fc9f0956b7d`.

Dean Cureton and Jesse Thorner directed the research and mathematical
judgments at Axiom Math. AxiomProver produced proofs and formalization.
The original package adapts material from OpenAI/math, Tau Ceti, LeanPool,
and the vendored class-field-theory development. Original source comments
and attribution are retained. The original and class-field-theory
Apache-2.0 licenses are preserved under `licenses/`.

## Actual theorem and scope

`Candidate.bound` states the Dedekind-zeta result for every number field
at boundary `31/32`: there exists a function holomorphic away from `1`,
agreeing with Mathlib's Dedekind zeta function on `Re(s) > 1`, and nonzero
on `Re(s) > 31/32` away from `1`.

`Candidate.hecke_bound` states the same boundary for finite-order Hecke
characters represented as ray class characters over every number field.
Nonprincipal characters include `s = 1`.

These are the genuine general-family statements from the imported source.
The current tracker's canonical target instead concerns Mathlib's Dirichlet
L-functions over all positive integer moduli. No theorem bridging these
representations is supplied in this draft, and the baseline's Dirichlet
result is not used as a substitute for Axiom Math's proof.

## Native proof package

The closure of `DedekindZetaZeroFree.Main` and `HeckeCorollary` comprises
5,508 Lean modules. They live under
`submissions/2026-10-12-axiommath-general-number-fields/src/Submissions/axiommath_general_number_fields/`.
Only local import paths change; declaration namespaces and proof bodies
are retained. In particular, native `public import` and `import all`
semantics are preserved.

`source-manifest.json` records the original paths and original/adapted
SHA-256 hashes. Original native configuration, README and formalization
metadata are archived under `upstream/`. The original challenge is
preserved under `Challenge/`: its intentional `sorry` placeholders declare
statements for Comparator and are never accepted as solution proofs.
The corresponding original solution is preserved with relocated imports.

The active native Lake package uses Lean `v4.35.0-rc3` and Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`. It points to the relocated
submission source and requires only the pinned Mathlib package: the complete
class-field-theory source closure is included locally and the proof roots
have no direct Tau Ceti imports. The unchanged original dependency
configuration, including Tau Ceti and the class-field-theory package,
is retained under `upstream/` for comparison.

From this directory, native reproduction is:

```sh
lake exe cache get
lake build
lake comparator --config comparator.json
```

These commands have not been run for the adapted source in this draft.

## Tracker integration status

The usual tracker verifier pins Lean `4.34.1` and Mathlib `d13f23b...`.
Its canonical challenge has a different statement, and its existing import
scanner does not account for native `import all` dependencies. As a result,
this submission is not ready for ordinary tracker admission. Native
source compatibility, dependency scanning, a general-family verification
profile or a faithful all-Dirichlet bridge, and independent Comparator/
kernel replay remain required before it can be represented as verified.

The value `31/32` expands the covered family; it does not improve the current
Dirichlet record. The draft does not alter verification policy or replace
its actual theorem with a weaker result derived from another submission.
