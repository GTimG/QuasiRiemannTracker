# Baiying Liu: three final targets independently checked

Liu's proof establishes the three nonvanishing families at the exact boundary
`(1507 − 2√921) / 1653`, approximately `0.8749570697991687400183400069588792241518`.
The pinned source is commit
[`7d10420de90efa2f082a06a342fc7accbd57ab37`](https://github.com/liubaiying101/Slightly-improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis/tree/7d10420de90efa2f082a06a342fc7accbd57ab37).
This package reconstructs and verifies that approach; it does not replace the
proof by a corollary of another contribution.

The fresh maintainer replay passed at **2026-10-10 09:10:59 UTC**. It rebuilt
all 238 selected modules in an offline Linux sandbox, exported the trusted
challenge before candidate execution, and checked the three exact targets with
Comparator, Lean, NanoDa and con-ron. Only `propext`, `Classical.choice` and
`Quot.sound` were allowed. The genuine filesystem/network/environment controls
passed. This reused an authenticated, read-only canonical library; it was not
an empty-cache bootstrap.

The [unchanged outside-sandbox receipt](../../public/proofs/liu-20261010-safe-replay/result.json),
[kernel log](../../public/proofs/liu-20261010-safe-replay/logs/judge.log),
[contract audit](../../public/proofs/liu-20261010-safe-replay/contract-audit.json)
and [sealed collection](../../public/proofs/liu-20261010-safe-replay/collection.json)
record this run. Its receipt SHA256 is
`15b550ed8dd47845a3afa96e87fa370c56221848ee648d757ac993f773eb4976`.
The current verification time refers to this confined maintainer run. The
earlier submitted report below remains historical evidence.

The contributor's earlier native build compiled 238 selected modules: 219 Liu modules and 19 OAI
modules absent from the existing cache. The original 22-target Lean entry then
passed a strict replay, using only `propext`, `Classical.choice`, and `Quot.sound`.
The original explicit-import inventory contains 13,820 source/configuration files
and 13,812 main `.olean` artifacts, with no missing explicit-source exemptions
and no `QRH` imports. A supplemental audit adds 95 compiler-provided implicit
`Init` modules: the corrected total is 13,915 source/configuration files and
13,907 main `.olean` objects, plus 21,488 `.olean.private`/`.olean.server`
sidecars (35,395 compiled inputs altogether). The supplement authenticates
compiler inputs against the pinned release archive and dependency-cache inputs
against freshly fetched official archives. The latter comparison covers all
8,908 official dependency-cache main objects and 17,816 sidecars; the pinned
compiler archive comparison covers 1,836 main objects and 3,672 sidecars. The
[compiler-input supplement](../../public/proofs/liu-20261010-kernels/compiler-input-supplements.json)
records the exact hashes and also covers all 8,130 optional parts of the
canonical-definition build. The historical manifest is retained
unchanged; its narrower count is not presented as a complete compiler inventory.
The earlier submitted Comparator report records acceptance by Lean, NanoDa
and con-ron of the three final targets at `2026-10-10T02:04:44.198552+00:00`. The
Comparator used separately built canonical definitions, allowed only the three
standard axioms, and passed the positive and negative controls. This is local
mechanical verification; no signed registry receipt or editorial acceptance is
claimed. The 22-target native replay and three-target independent replay have
different scopes.

[Verification evidence and scripts](../../public/proofs/liu-20261010-kernels/)
include the full build reports, module logs, replay logs, source fingerprints,
and a separate fresh-reconstruction test. The public metadata records path
neutralization and retains hashes of the original artifacts. The large exported
proof streams are not redistributed; their hashes are retained.

## Packaging repair and attribution

The pinned author repository omitted all 2,925 vendor modules declared in its
closure manifest, omitted `vendor/LICENSE`, and laid out several proof modules
outside their import namespaces. Our `prepare.py` restores the layout and reads
the exact vendor git objects at OpenAI/math
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. All declared SHA256 values and git blob
IDs match. No proof text was edited. Those 2,925 source hashes also match the
public accepted OpenAI/math revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

No LICENSE or redistribution grant was found in Liu's pinned repository or
README. This package therefore contains our reproduction tools and verification
evidence, with links to upstream. It contains no copied Liu Lean source or
exported proof data. The scripts fetch the source directly from its author.
The native dependency audit checks both pinned revisions and the exact
compatibility patches supplied by Liu; all 19 selected files from the two
patched dependencies match that reconstruction.

## Safe independent reproduction

Use the [maintainer sandboxed replay](../../verifier/liu/README.md):

```sh
/usr/bin/python3 verifier/liu/replay.py \
  --profile /srv/qrh/liu-worker-profile.json \
  --work /srv/qrh/runs/liu-fresh
```

The linked instructions specify the approved baseline, exact binary pins and
operator-owned profile. Every compilation that can load candidate code runs
inside genuine Linux isolation; the canonical challenge is exported first.
The driver's own receipt and logs are written outside candidate-writable paths.
A missing tool, unavailable sandbox or changed dependency is an infrastructure
blocker, never a reason to downgrade the required checks.

The immutable public dossier above describes the contributor's original run.
Its old `reproduce.py`, `build_native.py` and `verify_native.py` are historical
evidence, **not safe reproduction entrypoints**: native compilation inherited
the host environment, and `runpy.run_path` executed author Python to obtain its
target list. Do not run those scripts on an ordinary host. The new path never
executes author Python or Lake configuration and never writes a shared cache.
The old dossier remains unchanged so its evidence hashes remain meaningful.

The checked source theorems are:

- `CombinedPaper.algebraic_hecke_nonzero`
- `CombinedPaper.algebraic_dirichlet_nonzero`
- `CombinedPaper.algebraic_zeta_nonzero`

All come from `RHZeroFreeExtension.CombinedPaperVerification`. The Hecke and
Dirichlet principal-pole exceptions and Mathlib's total-value convention for
zeta at 1 are handled by the independent target statement, not altered in the
source proof. This package makes no claim to verify every manuscript statement
or the author's broader optimality assertions.

The historical compiler supplement retains the cache-key diagnostic and its
recorded hashes. The current replay consumes the reviewed cache keys as data,
checks their corresponding source hashes and downloads fresh official archives;
it does not execute the historical Lake diagnostic on the host.
