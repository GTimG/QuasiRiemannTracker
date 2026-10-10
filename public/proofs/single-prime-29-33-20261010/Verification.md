# New 29/33 analytic proof in ordinary Lean

The main new analytic route in `zeta_zero_free_4_33_self_contained.md` now
compiles in ordinary Lean. `ZetaZeroFree.Analytic.Final` constructs the actual
one-prime probe, proves its physical and error bounds, and proves
`HeckeZeroSupremum.beta <= 29/33`. It then proves nonvanishing for zeta,
every Dirichlet character of positive modulus, and finite-order Hecke
characters over the Eisenstein field, with the manuscript's pole exclusions.
The proof does not invoke the earlier terminal `7/8` result.

The complete verification passed at 2026-10-10T06:19:41.054096+00:00 with Lean 4.34.1
and `autoImplicit=false`. The audit checked all 1,087 declarations in
33 mathematical modules, including 703 theorems, and walked
124,307 reachable constants. Only `propext`, `Classical.choice`
and `Quot.sound` occur. No forbidden terminal dependency was found. The
standalone Appendix D.3 independence check also passed, traversing
100,736 constants. Fresh empty-environment kernel replay of
`ZetaZeroFree.Analytic.Final` returned zero.

The unconditional moment descent is ordinary readable Lean source. No
serialized proof loader remains in the mathematical modules. The main proof
and the stronger standalone mixed moment use the same unconditional endpoint.

## Reproduce the current proof

Run from the `formalization/` directory after the setup in `README.md`:

```sh
python3 verify_analytic.py
```

The default requires the unconditional final theorem, its zeta/Dirichlet/Hecke
endpoints, standalone Appendix D.3, and the actual normalized physical and
whole-band estimates. It builds `ZetaZeroFree/Exponent` and every mathematical
module under `ZetaZeroFree/Analytic`, checks every declaration
including private helpers, permits only `propext`, `Classical.choice` and
`Quot.sound`, and walks their complete transitive type and proof dependencies.
It rejects the older terminal theorem even when hidden behind a helper.
A separate dependency gate prevents Appendix D.3 from using either terminal
zero-free theorem or the former beta-dependent moment and prime endpoints.
It then runs:

```sh
elan run leanprover/lean4:v4.34.1 lake env leanchecker --fresh --verbose ZetaZeroFree.Analytic.Final
```

`leanchecker` uses Lean's own kernel, starting with an empty mathematical
environment. Unsafe and partial program definitions are excluded by that tool;
it is a mathematical kernel replay, not an independent external kernel.
The runner checks that the exact source and compiled artifact hashes remain
unchanged during verification, and rejects additions or removals from the
mathematical module inventory during the run. `--core` is explicitly a partial-progress audit
and cannot report the full endpoint as complete.

## Independent kernel verification

The contributor's local Comparator run **passed on 2026-10-10T07:47:35.881822+00:00**.
Lean's default export kernel, NanoDa and con-ron all accepted the Solution.
The complete run took 749.6 seconds; con-ron reported
121,558 accepted exported declarations. This count has a different scope from
the full ordinary-Lean declaration audit above.

The four selected roots are `SinglePrime2933.allDirichlet`, `.zeta`, `.allHecke`
and `.appendixD3`. They wrap the three nonvanishing endpoints and the standalone
mixed moment without adding assumptions. Principal pole exclusions remain in
the statements. Comparator checked their theorem types and the constants and
definition bodies reached from those types. No definition holes are permitted.
Its transitive Solution axiom check allows only `propext`, `Classical.choice`
and `Quot.sound`. Challenge's deliberate `sorry` bodies are specification
placeholders; they are not proofs and are not used as Solution axioms.

This verifies the four proof closures, not every unused helper theorem. The
original dependency audits remain the evidence for excluding the old terminal
7/8 proof and circular Appendix D.3 dependencies. Kernel checking alone does
not establish that the statements faithfully represent the manuscript.

Sources were compiled with Lean **4.34.1**, exported with pinned lean4export,
and checked with the official **4.35.0-rc2** bundle. A valid-proof control was
accepted; a changed theorem statement and an ill-typed proof were rejected.
The executed proof sources and compiled artifacts were checked against the
original report before and after verification. Exact pins, source wrappers,
configuration, transcripts, resource receipts and hashes are in
`evidence/multi-kernel/`; start with its `README.md` and `result.json`.

This is local contributor evidence, not Palomar registry admission or a signed
maintainer receipt. It uses official Comparator's built-in kernel sandboxes
under a 32 GiB / four-CPU cgroup, without Palomar's additional outer judge
sandbox. Host security settings were unchanged. The older source compiler and
the Challenge's pinned OpenAI/local definitions are outside the current signed
submission route. Repository status remains pending maintainer review.

The 666,577,664-byte Challenge export and 1,664,082,892-byte Solution export are
omitted from this source bundle; their SHA-256 hashes are in `export-pins.json`.

## Analytic coverage

| Module | Actual proved content |
| --- | --- |
| `Starter/Inverse`, `Starter/Nonvanishing` | Unconditional inverse raw moment, sixth-power amplification, singleton estimate, Mellin continuation and the independent starting bound `beta <= 11/12`. |
| `Energy/Geometry`, `WholeIndex`, `CompletedSource` | New scales `M=28/33`, `ell=5/33`, `Nstar=38/33`, exact whole-index coefficient transport, and completed energy with arbitrary positive final loss. |
| `Energy/PhysicalSource`, `GaussianSource` | Actual marked and unmarked physical slices, reciprocal normalizer, and the complete compensated probe bound `O(Z^(20/99+epsilon))`, including near and remote Gaussian dyads. |
| `Moments/Plain`, `Exceptional`, `Source` | Moving-mask and independent-height controls; fixed nonprincipal inducing rows; exact source coefficient/orientation identities; arbitrary finite source rows. |
| `Moments/Unconditional` | Genuine contour-at-one estimate and unconditional finite effective-width descent, with uniform smooth orders and fixed-row restoration. |
| `Moments/FixedFactor`, `Sharp`, `CompactProfiles`, `Presentation`, `AppendixD3` | Exact standalone moving-radical mixed moment, common punctures, retained coefficient zeros, sharp finite row sums, separate lengths/heights and uniform compact C^J norms. |
| `Rows/Witness`, `Count`, `UniformProfiles`, `SourceCount` | Same-zero two-polynomial witnesses, uniformly controlled raw profiles, actual plain moment input and optimized unmarked `R0` row count. Both polynomial orders are selected before the contour height and target character. |
| `Principal/Signal`, `Residues` | Actual one-prime principal comparison at `k=67/99`, nonzero normalizer and strict residue savings. |
| `Probe/Transport`, `Central`, `Collected`, `Assembly`, `Band` | Exact physical partition, contour transport, small and infinite large tails, central cells and finite shell/bin aggregation at the new scales, with no assumed count or moment in the completed Band wrapper. |
| `SourceData`, `Parameters` | Common source/window/exclusion set and explicit positive losses fixed before the target; height choices follow the uniform polynomial orders. |
| `Continuation`, `Final` | Regularized Mellin continuation at the principal pole, finite Euler deletion transfer, nonattained-supremum contradiction, unconditional `beta <= 29/33`, and final nonvanishing statements. |
| `ZetaZeroFree/Exponent` | Exact rational scale identities, square certificate, positive slope and common-loss arithmetic. |

The central band is bounded by `Z^(20/99+11u)`. The reciprocal normalizer costs
`Z^u`, and the explicit common parameters prove
`21u+sigma < (beta-29/33)/2`. The physical estimate uses the positive loss
`(beta-29/33)/4`. All parameters and source data precede the target character;
only bound constants and eventual thresholds may depend on that target.

## Faithfulness of the moment theorem

`Moments.D3.mixed_plain_moment_radical` proves the standalone mixed moment
in Appendix D.3. Its smooth order, constant and eventual threshold are fixed
before the moving character, support indexing set, exponents, puncture, finite
row set, profiles, lengths and independent norm-twist heights. The exponent is
exactly `m + q + epsilon`; each length is bounded individually, with no lower
conductor condition or product-length restriction. The profile dependence is
`||W1||_(C^J)^2 ||W2||_(C^J)^2`.

The coefficient identity holds on every ideal, including all prescribed
zeros. The fixed base character incorporates the manuscript's fixed bad-prime
exclusion. Indexing each distinct moving support prime once gives the radical
cost. Sextic exponents use positive representatives: residue zero is represented
by six, which retains the zero on a nonunit. These are the manuscript's
standing zero-retention conventions, not extra analytic hypotheses.

The unconditional descent uses a genuine contour estimate at `a = 1` and
`kappa = 1`, requiring only the elementary upper bound `beta <= 1`. It does
not assume `beta >= 51/100` and does not use the final zero-free theorem. The
previous conditional moment wrappers have been removed, and the main proof
now uses this unconditional endpoint. The dedicated D.3 dependency gate checks
both old and new terminal bounds, the superseded wrappers, the old beta-based
prime estimate, and disposable extraction modules.

The proof reuses intermediate analytic foundations in the pinned OpenAI
library, including finite descent, functional equations and source controls.
Names containing `SevenEighths` belong to that library's historical namespace;
the dependency gate examines the actual declarations. The one-prime principal
comparison uses admissible contours `w = 19/20` and `z = 33/200`. The band
retains the manuscript's full `delta <= 5/6` range, using the independent
`11/12` starting bound. The formalization follows this analytic route with the
explicit contour choices above.

## Verification evidence

- `evidence/analytic-verification-report.json`: completed build, full declaration
  audit and fresh kernel replay, with exact source/artifact hashes and outputs.
- `evidence/final-audit.lean`: the actual generated final audit input.
- `evidence/current-provenance.json`: source contexts, changes and input hashes.
- `evidence/analytic-gate-controls.json` and `evidence/negative-controls/`:
  admission, custom-axiom, missing-root, old-terminal and D.3 circularity controls.
- `publication-transformations.json`: host-path redaction receipts. Mathematical
  sources and their reported hashes are unchanged.
- `evidence/import-closure.json`: exact vendored OAI and local source closure.

The controls refer to their original temporary paths symbolically; the copied
inputs/logs can be found by basename in `evidence/negative-controls/`. Old
partial reports and superseded proof representations are not part of this
current publication snapshot.

## Weighted-numerator reference

The supplied reference is pinned at
[QuasiRiemannTracker commit 2fd60c0](https://github.com/akashlevy/QuasiRiemannTracker/tree/2fd60c0926b66ea18d7436f5ed55250fd006ab5d/proofs/akashlevy-20261009-weighted-numerator).
Its stronger `10499/12000` result uses the earlier `7/8` background inside
`WeightedQRH/MomentTerminalInput.lean`, and its high-row certificate is limited
to `a <= 7/8`. Its coefficient and reflected-orientation identities are useful
references, but no source from that package is imported into this proof.
External kernel reports in its README are author-reported evidence and were
not independently rerun here. The public GitHub API returned no pull requests
at this review's read; this is a timestamped observation, not a permanent
claim about repository activity.

## Toolchain, source and historical checks

The proof uses ordinary Lean 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and OpenAI math at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The dependencies are pinned by
`lake-manifest.json`: Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`,
PrimeNumberTheoremAnd `c39a751132c88b6e8080b74c74023fd95b3d8be0`, and
rellich-kondrachov `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`.
The latter two retain the upstream Lean 4.34.1 compatibility patches.
`evidence/current-provenance.json` preserves the supplied-document hashes and
current source provenance. The publication revision adds Hailey Collet's
authorship, contact details and GPT-6 Pro assistance credit. Its source changes
and rebuilt PDF hashes are recorded in `manuscript/rendered-documents.json`;
the mathematical text, Lean sources and kernel evidence are unchanged.

The publication snapshot replaces the original local source symlink with
the exact required OAI source files. The local cache is excluded. Use the
bundled bootstrap script, manifest and compatibility patches to set up a new
environment. This packaging pass does not claim a second clean-machine build.

The adapted OpenAI license is retained in `licenses/LICENSE.OpenAI-Lean`;
see `NOTICE.md` for source modifications and manuscript-rights status.
