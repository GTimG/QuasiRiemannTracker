Independent mechanical verification of the exact algebraic endpoint

The actual local Palomar mechanical run accepted seven targets at
2026-10-09T19:51:12.662856+00:00: three rational N36 bounds, three exact algebraic
bounds, and unique existence of the root defining the threshold. Comparator
compared statements and definitions; con-ron, NanoDa and Lean's fresh kernel
accepted the exported proofs. Positive and both negative controls are retained.
Only propext, Classical.choice and Quot.sound were permitted. No definition
holes, altered core verifier, skipped kernels or fake preflight were used.

Source commit: 2fc2b0b7f2b9510df4618936e1b2ccd58f7d9171
Source manifest: bccaf56bd16eaa2f8d0581df5db8bb81d21cc583a7093bba4b3b51793b70fa5d
Source archive: 9ceab677dedfc3065bb45d741a24542d3b8de68de957727c84b0aaa5a243f23a
Frozen wrapper manifest: 053812f0bf8d395ce66093862bd2207b6eff6f9ba62422b84d1896f61f112303

This is an exact algebraic endpoint follow-up to the merged N24 compressed
rational refinement. Its earlier accepted record and evidence remain intact.
Independent replay covers the seven statements and their proof dependencies.
Other unused declarations and the previous original/N24 implementations retain
their separate native checks. The exact and N36 targets also imply the older
bounds mathematically. Old source and evidence snapshots remain immutable.

The source compiler/exporter uses Lean4.34.1; the judge and kernels use pinned
Lean4.35.0-rc2. Build-inputs records source/olean rehashing, actual LEAN_PATH
resolution, published Git-blob equality, and pinned mathematical definitions.
The driver repeated its frozen-build checks after acceptance. Source was
committed locally before the run; remote publication is a later separate step.

The sandbox used a temporary path-specific AppArmor profile for the root-owned
pinned bubblewrap binary. Proof code ran unprivileged. Global userns restrictions
were unchanged; provisioning and completed cleanup evidence are included.
The provisioning observation was recorded during this algebraic run. The
Challenge and checker source audits retain their historical timestamps; the
new driver freshly revalidated the identical pinned imports, artifacts and
checker code rather than relabeling those earlier observations as new checks.

This is a local mechanical result, not Palomar registration, editorial approval
or a signed tracker admission. The catalogue proposal is subject to maintainer
review. Native-only source collection labels are preserved as historical status.

To reproduce, follow the source snapshot README, install the checker tools at
their recorded hashes, place verify_algebraic.py under WORKSPACE/tightening-research/checkers,
and copy checker-binary-pins.json to that directory as tool-pins.json. The dossier's
tool-pins.json is the accepted run's nested metadata, not that flat input file.
Extract the previous N24 source snapshot into WORKSPACE and the new algebraic
snapshot into WORKSPACE/algebraic-proof. The driver reads the old accepted
local-selected-source-graph.json and local-build-records.json from
WORKSPACE/compressed/audit. Copy the byte-identical published N24 checker
build-inputs.json from TRACKER/public/proofs/nielstron-20261009-kernels into
WORKSPACE/tightening-research/checkers/runs/candidate-n24-r2/build-inputs.json.
Those three publicly available files bind the shared Challenge import closure;
no private Git repository or private history is needed.
Use a disposable Linux worker with genuine nested sandbox support. Run:

python3 verify_algebraic.py --candidate WORKSPACE/algebraic-proof/compressed --run-id fresh-algebraic \
  --source-manifest bccaf56bd16eaa2f8d0581df5db8bb81d21cc583a7093bba4b3b51793b70fa5d \
  --published-source-commit 2fc2b0b7f2b9510df4618936e1b2ccd58f7d9171 \
  --published-checkout TRACKER --published-prefix proofs/nielstron-algebraic-20261009/compressed/formalization \
  --wrapper-sources TRACKER/proofs/nielstron-algebraic-20261009/verification/src \
  --wrapper-manifest 053812f0bf8d395ce66093862bd2207b6eff6f9ba62422b84d1896f61f112303

Supply the documented --bwrap and temporary profile options where applicable.
Do not disable preflight or any kernel. The script refuses an existing run
directory. Large proof exports are omitted here with their actual sizes and
SHA256 digests; regenerate them from the frozen source. Runtime workspace prefixes
are neutralized with original/published hashes preserved in the transformation
record. Website validators authenticate this evidence; they do not rerun proofs.
