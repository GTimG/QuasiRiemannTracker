# Local moment research revision 2

11 October 2026. Zhongpai Gao, with AI assistance.

The full analytic theorem is **not complete**. This revision supplies actual
incumbent inverse profiles and a supported-witness constructor, pays fixed
label/dyadic costs, and gives a general mathematical reconstruction bound.
It preserves the first research snapshot and its reports.

Read the human-readable manuscript in [paper.tex](paper.tex) (Draft 2).
Compile it with `tectonic paper.tex`, or run `pdflatex paper.tex` twice.
The PDF is generated from this source; binary build outputs are not included.
The [predecessor snapshot](../gao-local-moment-20261011/README.md) retains the
exact endpoint/source audits and original input pins.

## New compiled results

`formalization/LocalMoment/ActualUnmarkedInputs.lean` proves:

- `fixed_family_inverse_raw`: a single incumbent inverse-profile constant for
  a fixed finite `RowData` family, uniformly in scale, orientation and frequency.
- `batch_moments_of_plain_unmarked`: with that inverse input supplied, a plain
  unmarked estimate suffices to construct the batch's moment fields.
- `unmarked_batch_from_actual_maxima`: a batch constructed from actual buffered
  maxima on the nonempty supported set, retaining the nonprincipal, conductor,
  row-norm and coefficient conditions as explicit application hypotheses.
- `fixed_label_dyadic_cost`: both dyadic lengths and the fixed label cardinality
  are paid at an arbitrarily small power cost.

The derivative profile in `UnmarkedDensity` is now explicitly resolved to
`HeckeDetectorRowwisePolynomial.logProfile`. The old structure allowed that
name to be implicitly generalized; the new interface names the intended
profile operation directly. `ActualUnmarkedInputs` disables automatic implicit
parameters to catch unresolved identifiers.

Nine source components plus the audit module were freshly compiled with the
pinned Lean 4.34.1 compiler. Sixteen named axiom checks report only `propext`,
`Classical.choice` and `Quot.sound`. Cached dependencies were reused. This is
development evidence, not independent maintainer or three-kernel acceptance.

## Analytic progress and remaining work

Read [ANALYTIC_RECONSTRUCTION.md](ANALYTIC_RECONSTRUCTION.md). It proves a
general bound for ideals of prescribed prime support and the resulting joint
label count under the explicit effective-row factorization. It also aligns
the left/right phase convention with the literal upstream Lean definitions.
That arithmetic argument is written mathematics; it is not included in the
sixteen Lean axiom checks.

The major remaining obligations are:

1. Generalize the actual plain zero-slot source and eligibility adapter to
   the unmarked batch, including small-core rows and uniform constants.
2. Prove the signed character/effective-row identity and the allocation
   hypotheses for the complete physical source, retaining both Euler masks.
3. Complete comparison/exceptional estimates and the full common Fourier,
   profile and independent-height assembly.
4. Prove the ordinary all-family endpoint and obtain canonical comparison
   and independent kernel acceptance.

In particular, the original adapter's marked-batch assumptions do not vanish
when its selected prime product is empty. This is an unresolved mathematical
interface, not a request to relax the target or add an axiom.

## Replay

Supply the compiler and exact dependency libraries from the pinned source
environment described in the predecessor package. Then run:

```sh
python3 replay_components.py --lean /path/to/lean-4.34.1/bin/lean \
  --library /path/to/mathlib/lib/lean --library /path/to/OAI/lib/lean \
  --library /path/to/other-dependencies/lib/lean --work-dir /new/empty/directory
```

Repeat `--library` for each required dependency. The runner authenticates the
compiler, copies only these local sources into the new work directory, compiles
all components, and checks the reported axiom sets. It does not rebuild imported
dependencies, download or execute upstream scripts, or certify the final target.

For the exact source and endpoint audits, retain the predecessor package's
original instructions and pinned inputs. This revision does not alter those
certificates or turn them into a proof of the analytic theorem.

The public evidence report replaces machine-specific dependency paths by
library labels; all component source, object and log hashes are retained.
The untouched local replay report remains in the development build directory.
