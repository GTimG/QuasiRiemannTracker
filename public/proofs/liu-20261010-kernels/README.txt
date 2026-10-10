# Baiying Liu: three final targets independently checked

Liu's proof establishes the three nonvanishing families at the exact boundary
`(1507 − 2√921) / 1653`, approximately `0.8749570697991687400183400069588792241518`.
The pinned source is commit
[`7d10420de90efa2f082a06a342fc7accbd57ab37`](https://github.com/liubaiying101/Slightly-improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis/tree/7d10420de90efa2f082a06a342fc7accbd57ab37).
This package reconstructs and verifies that approach; it does not replace the
proof by a corollary of another contribution.

The native build compiled 238 selected modules: 219 Liu modules and 19 OAI
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
The independent Comparator and all three kernels—Lean, NanoDa, and con-ron—
accepted the three final targets at `2026-10-10T02:04:44.198552+00:00`. The
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

## Reproduce from public inputs

The scripts are in
[`public/proofs/liu-20261010-kernels`](../../public/proofs/liu-20261010-kernels/).
Use Linux with Python 3.11+, Git, tar, zstd, and the pinned Lean 4.34.1 compiler.
The following uses the already published tracker snapshot to reconstruct the
compiler and dependency cache; it needs no private repository. Run from a clone
containing this proof package and the published baseline. Copy the baseline to
a scratch directory first: its builder rewrites local build inventories. Keep
the published snapshot unchanged for the independent canonical audit pins.

```sh
cp -a proofs/nielstron-20261009-tightening replay-baseline
python3 replay-baseline/tools/setup_workspace.py --with-dependencies
python3 public/proofs/liu-20261010-kernels/reproduce.py --work replay-liu
```

Build the declared OAI foundation against the published baseline's pinned
sources and official Mathlib cache. This command does not compile or import a
QRH theorem into Liu's proof:

```sh
python3 - <<'PY'
import json, subprocess, sys
from pathlib import Path
baseline = Path('replay-baseline')
manifest = json.loads(Path('replay-liu/package/upstream/closure_manifest.json').read_text())
subprocess.run([sys.executable, str(baseline/'compressed/scripts/build_cached.py'),
                *sorted(manifest['modules']), '--jobs', '8'], check=True)
PY
python3 public/proofs/liu-20261010-kernels/build_native.py \
  --package replay-liu/package \
  --lean replay-baseline/compressed/toolchains/lean-4.34.1-linux/bin/lean \
  --lean-path-file replay-baseline/compressed/audit/local-lean-path.txt \
  --workers 8
python3 public/proofs/liu-20261010-kernels/verify_native.py --work replay-liu --workers 8
python3 public/proofs/liu-20261010-kernels/inventory.py \
  --work replay-liu --source-root "$PWD" \
  --dependencies replay-baseline/compressed/formalization/.lake/packages
```

The original native build and strict replay above were performed with the same
pinned compiler, source bytes, patches, and explicit cache boundary. The complete
public-baseline bootstrap plus all foundation compilation has not been rerun in
a second empty cache. A separate fresh directory did fetch both exact upstream
commits over HTTPS, reconstruct the identical package, authenticate and rehash
all recorded input files/artifacts, and replay the original 22-target entry.
That test reused the authenticated compiled artifacts and is labelled as such.
Its historical inventory preceded the supplemental compiler audit. The original
executed inventory script is retained as `inventory-olean-only-executed.py`;
`inventory.py` is the corrected reproduction version, including implicit `Init`
and optional sidecars. No mathematical source changed.

The author's Python `verify.py` Lake frontend was not run to completion. Our
tested native driver uses its original target inventory and unmodified Lean
entry. It does not run `lake update` or silently rewrite the dependency manifest.
A cached native replay alone is not independent kernel verification; the
separate checker must recheck the exported proof and compare its definitions.

## Independent checker replay

The shared [`verify_external.py`](../../public/proofs/liu-20261010-kernels/verify_external.py)
compiles the canonical challenge separately from the candidate. The immutable
canonical audit files remain in `proofs/nielstron-20261009-tightening`; the actual
compiler artifacts are regenerated under `replay-baseline/compressed`.

Prepare the checker layout documented in the existing
[checker setup notes](../../public/proofs/nielstron-20261009-kernels/README.txt).
The source repositories are
[PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission) at
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` and
[lean4export](https://github.com/leanprover/lean4export) at
`076e8e57707e813375e8f9da8bf989799ace9680`. The exporter uses Lean 4.34.1;
the judge bundle is Lean 4.35.0-rc2. Place them under `replay-checkers/tools/`
with names `palomar`, `lean4export`, and `lean-4.35.0-rc2-linux`. Copy the earlier
`checker-binary-pins.json` to `replay-checkers/tool-pins.json`: that flat input is
different from the nested run metadata named `tool-pins.json`. Use the exact
pinned bubblewrap binary in a disposable Linux worker with genuine nested
sandbox support. The driver checks binary hashes, positive/negative controls,
and all kernels; it does not provide a preflight bypass.

Create a new configuration from the rebuilt local inputs and the published
wrapper sources, rather than reusing paths from the recorded machine:

```sh
python3 - <<'PY'
import hashlib, json, shutil
from pathlib import Path
root = Path.cwd()
evidence = root/'public/proofs/liu-20261010-kernels'
report = json.loads((evidence/'result.json').read_text())
inventory = json.loads((root/'replay-liu/judge-input-inventory.json').read_text())
wrappers = root/'replay-liu/wrappers'
wrappers.mkdir(exist_ok=True)
for name, key in [('Challenge.lean', 'challenge_source'), ('Solution.lean', 'solution_source')]:
    shutil.copyfile(evidence/report[key], wrappers/name)
base = root/'replay-baseline/compressed'
config = {
    'repository': 'liubaiying101/Slightly-improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis',
    'source_commit': '7d10420de90efa2f082a06a342fc7accbd57ab37',
    'theta_exact': '(1507 − 2√921) / 1653',
    'source_manifest_sha256': inventory['source_manifest_sha256'],
    'input_inventory': str(root/'replay-liu/judge-input-inventory.json'),
    'source_root': str(root),
    'source_checkout': str(root/'replay-liu/liu-source'),
    'native_build_report': str(root/'replay-liu/native-verification.json'),
    'canonical_root': str(base),
    'canonical_audit_root': str(root/'proofs/nielstron-20261009-tightening/compressed/audit'),
    'canonical_lean_path': str(base/'audit/local-lean-path.txt'),
    'candidate_lean_path': str(root/'replay-liu/native/lean-path.txt'),
    'source_toolchain': str(base/'toolchains/lean-4.34.1-linux'),
    'wrapper_sources': str(wrappers),
    'challenge_sha256': hashlib.sha256((wrappers/'Challenge.lean').read_bytes()).hexdigest(),
    'source_provenance': str(evidence/'reconstruction-provenance.json'),
    'reproduction_script': 'reproduce.py',
    'workspace': str(root),
}
(root/'replay-liu/judge-config.json').write_text(json.dumps(config, indent=2)+'\n')
PY
python3 public/proofs/liu-20261010-kernels/verify_external.py \
  --config replay-liu/judge-config.json --work replay-liu-kernel-run \
  --checkers replay-checkers --bwrap /absolute/path/to/pinned/bwrap --jobs 8
```

The checker refuses an existing run directory. Its output reports actual new
results; the archived report is evidence of the recorded run. These instructions
have not been executed as one clean end-to-end run from the public package.

The checked source theorems are:

- `CombinedPaper.algebraic_hecke_nonzero`
- `CombinedPaper.algebraic_dirichlet_nonzero`
- `CombinedPaper.algebraic_zeta_nonzero`

All come from `RHZeroFreeExtension.CombinedPaperVerification`. The Hecke and
Dirichlet principal-pole exceptions and Mathlib's total-value convention for
zeta at 1 are handled by the independent target statement, not altered in the
source proof. This package makes no claim to verify every manuscript statement
or the author's broader optimality assertions.

The compiler supplement includes `cache-key-generator.lean.txt`, our diagnostic
helper for obtaining source-derived official cache keys, not a Liu proof. For
that diagnostic, rename it to `CacheKeys.lean` in a scratch directory and run
`lake env lean --run /absolute/path/to/CacheKeys.lean` from the pinned Mathlib
checkout; the exact source-search environment, script SHA256, and output-map
hash are recorded in `mathlib-cache-key-source-audit.json`. The fresh HTTPS
download and isolated extraction reports retain the subsequent provenance links.
