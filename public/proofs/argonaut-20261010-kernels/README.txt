ARGONAUT MATH: INDEPENDENT VERIFICATION DOSSIER

Status: Comparator and all three independent kernels accepted the three final
targets at 2026-10-10T02:21:37.471247+00:00. See result.json and judge.log for the
actual run. Only propext, Classical.choice and Quot.sound were permitted.

Original contribution: Argonaut Math, perturbed boundary 3499999/4000000.
Source repository:
https://github.com/Argonaut-Math/argonaut-math-quasi-riemann-boundary
Pinned commit: 5971383edcb0b1cf863927eed3b359d2d3ba346e
Original release: v0.1.8, Lean_Proof_Source.zip
Original release SHA256:
37602f9379f833c1b9ad3a6c7c628f961670f4219a9ac0f4190f8eb9b7655a93

The source-public.tar.gz download preserves the exact proof-addition bytes,
original notices and dependency pins from the reviewed compact source package.
It contains 178 files, including 139 original Lean source files. It does not
repeat the 135 MB expanded dependency overlay. source-package-review.json
records its complete member inventory, publication checks and transformation
from the compact ZIP; SOURCE-SHA256SUMS.txt authenticates the download.

To reproduce the original source:
1. Extract source-public.tar.gz into a fresh directory.
2. In argonaut-v0.1.8-reviewed-source, run:
   python3 reproducibility/fetch_original.py --output ORIGINAL
3. Follow ORIGINAL/Lean_Proof/BUILD.md using Lean 4.34.1 and the exact 42
   dependency pins. The fetcher verifies the original archive size and SHA256;
   the original reconstruction script verifies its nested source overlay.
4. Build PerturbedBoundaryMain and run the original theorem/axiom audits.

The recorded native reproduction compiled 152 modules freshly and reused
13,669 individually source-matched dependency/foundation modules. Both original
Argonaut theorem/axiom audits passed. It is not presented as a clean, cache-free
Lake build of every dependency. native/ retains the exact scheduler and audit
scripts as executed; their operator layout and cache inputs are explicit in
the reconstructed metadata and native-lean-path.txt. The public reconstruction
check separately fetched the exact release and matched all 12,055 restored
source-overlay files before replaying the original audits.

The three original targets are the all-Dirichlet, zeta and finite-order
Eisenstein Hecke conclusions at the exact rational boundary. Comparator compared
their statements and actual definitions against a separately compiled canonical
challenge; Lean, NanoDa and con-ron then accepted the exported proof. Matching,
mismatched-statement and ill-typed controls passed.
No stronger local proof or another contribution is substituted for this source.

Canonical definition audit: the independent challenge uses the pinned OpenAI
and Mathlib definitions. Its reference audit metadata is the immutable published
proofs/nielstron-20261009-tightening/compressed/audit snapshot, not subsequently
regenerated working QRH audit files. Regenerated local build logs are separate
run evidence. Actual canonical dependency source and artifact hashes must match
that published reference; no candidate QRH import is admitted into the challenge.
The source compiler and independent checker toolchain are pinned separately.

Complete audit metadata: metadata/metadata-manifest.json binds the original
operator inventory, native source/build graph, reused-foundation inventory and
the full import-resolution audit. Their UTF-8 content is split on complete
lines into gzip chunks of at most 4 MiB expanded size. Every expanded chunk and
the complete original record were checked by the repository publication policy.
To reconstruct readable JSON records with portable WORKSPACE labels, run:
  python3 reassemble_metadata.py metadata RECONSTRUCTED_METADATA
Use --workspace /home/niels/riemann to restore the exact original paths and
verify the original whole-file hashes as well. No proof exports or compiled
Lean artifacts are contained in these metadata chunks.

The independent checker driver and resolution/judge-config.json retain the
original run interface. To replay it, reconstruct the original source and
independent canonical build, restore the recorded WORKSPACE path mapping, and
provide the pinned Palomar/checker tools and bubblewrap binary. The source
compiler is Lean 4.34.1; the independent checker is Lean 4.35.0-rc2, NanoDa and
con-ron. The config's wait_for_report field only serialized two local heavy
checks; it can be omitted when replaying this contribution alone. The exact
executed driver bytes and both proof-export digests remain authenticated.

Concrete independent-checker replay:

The public baseline and checker setup are already retained in the tracker:
  proofs/nielstron-20261009-tightening/README.md
  public/proofs/nielstron-20261009-kernels/README.txt
Copy the baseline to scratch before running its setup tool, because its builder
regenerates local inventories. Keep the published canonical audit unchanged:

  cp -a proofs/nielstron-20261009-tightening replay-baseline
  python3 replay-baseline/tools/setup_workspace.py --with-dependencies

Prepare PalomarSubmission at d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44,
https://github.com/PalomarRegistry/PalomarSubmission, and lean4export at
076e8e57707e813375e8f9da8bf989799ace9680,
https://github.com/leanprover/lean4export. Place the pinned tools under
replay-checkers/tools/palomar, replay-checkers/tools/lean4export and
replay-checkers/tools/lean-4.35.0-rc2-linux. Copy the earlier dossier's flat
checker-binary-pins.json to replay-checkers/tool-pins.json; this differs from the
nested tool-pins.json describing this run. Use the pinned bubblewrap binary in
a disposable Linux worker with genuine nested sandbox support.

After the original source reconstruction and native build, provide this layout:
  replay-argonaut/upstream/                 Git checkout at the pinned commit
  replay-argonaut/evidence/operator-inventory.json
  replay-argonaut/evidence/native-build.json
  replay-argonaut/native/lean-path.txt       actual rebuilt candidate import path
These must describe the new build. The retained native/tools scripts document
the executed build/inventory process and its operator layout; old artifact
hashes are evidence of the recorded run, not substitutes for a fresh inventory.
The following adapts the checker configuration to the rebuilt paths and copies
the exact published wrappers. Run from the tracker clone containing this dossier:

python3 - <<'PY'
import hashlib, json, shutil
from pathlib import Path
root = Path.cwd()
evidence = root/'public/proofs/argonaut-20261010-kernels'
candidate = root/'replay-argonaut'
inventory_path = candidate/'evidence/operator-inventory.json'
inventory = json.loads(inventory_path.read_text())
report = json.loads((evidence/'result.json').read_text())
wrappers = candidate/'wrappers'
wrappers.mkdir(exist_ok=True)
for name, key in [('Challenge.lean', 'challenge_source'), ('Solution.lean', 'solution_source')]:
    shutil.copyfile(evidence/report[key], wrappers/name)
base = root/'replay-baseline/compressed'
config = {
    'repository': 'Argonaut-Math/argonaut-math-quasi-riemann-boundary',
    'source_commit': '5971383edcb0b1cf863927eed3b359d2d3ba346e',
    'theta': '3499999/4000000',
    'source_manifest_sha256': inventory['source_manifest_sha256'],
    'input_inventory': str(inventory_path),
    'source_root': inventory['source_root'],
    'source_checkout': str(candidate/'upstream'),
    'native_build_report': str(candidate/'evidence/native-build.json'),
    'canonical_root': str(base),
    'canonical_audit_root': str(root/'proofs/nielstron-20261009-tightening/compressed/audit'),
    'canonical_lean_path': str(base/'audit/local-lean-path.txt'),
    'candidate_lean_path': str(candidate/'native/lean-path.txt'),
    'source_toolchain': str(base/'toolchains/lean-4.34.1-linux'),
    'wrapper_sources': str(wrappers),
    'challenge_sha256': hashlib.sha256((wrappers/'Challenge.lean').read_bytes()).hexdigest(),
    'source_provenance': str(evidence/'original-source-provenance.json'),
    'reproduction_script': 'fetch_source.py',
    'workspace': str(root),
}
(candidate/'judge-config.json').write_text(json.dumps(config, indent=2)+'\n')
PY
python3 public/proofs/argonaut-20261010-kernels/verify_external.py \
  --config replay-argonaut/judge-config.json --work replay-argonaut-kernel-run \
  --checkers replay-checkers --bwrap /absolute/path/to/pinned/bwrap --jobs 16

The driver refuses an existing run directory and does not bypass the positive
or negative controls. The original native build, source reconstruction test and
independent checker run were performed. This entire public-baseline bootstrap
plus candidate foundation build and checker recipe has not been rerun from an
empty cache. The fresh source-reconstruction test reused authenticated compiled
artifacts when replaying the original audits; its report states that scope.

Import auditing distinguishes main .olean files from .olean.private and
.olean.server sidecars loaded by Lean 4.34.1. The immutable canonical audit
pins its original main .olean records; supplementary sidecar provenance uses
the independently downloaded official Mathlib master cache and pinned Lean
release archive. This is recorded separately from the mathematical checker
verdict and does not infer sidecar provenance from a matching main-file hash.

Authorship and licensing: the mathematical proof is Argonaut Math's work on
the OpenAI framework. Original Apache-2.0 and dependency notices are retained
in the archive and notices/. This verification packaging is separate from the
proof. It creates no signed tracker receipt or Palomar registration.
