Independent mechanical checks for Nielstron's exact N24 refinement

The recorded local Palomar mechanical run passed the fixed three-target Comparator
comparison and Lean's fresh kernel, NanoDa, and con-ron. The positive control passed;
the mismatched-statement and ill-typed-proof controls were rejected as required.
Only propext, Classical.choice and Quot.sound were permitted, with no definition holes.

Checked source commit: 49331e02e2c04bb2388ae9c6e9ea424c23b96ac6
Source manifest SHA256: eeef7d35e9437ad2ad5180be09bbaecf8e0403f8c16b399b868bf21818d176ed
Immutable source archive SHA256: 4388d6e63f0127ce12a116ead3ffecbdc1db2a0d33b5da15993c206c69896dd4
The source snapshot remains under proofs/nielstron-20261009-tightening. Its older
native reports and pending labels are preserved as historical evidence. This new
dossier records the later checker acceptance; it does not alter the proof.

Independent kernel replay covers the three stronger all-Dirichlet, zeta and Hecke
targets and their exported proof dependencies. It does not separately replay every
unused QRH declaration, older-bound theorem or ZeroBounds implementation; those
retain the recorded native Lean checks. The stronger targets mathematically imply
the older bound, and both exact target families passed the native Lean gates.

Lean4.34.1 and its pinned exporter produced the exports. The judge and three kernels
are pinned Lean4.35.0-rc2 binaries. Tool hashes and runner source are retained.
Namespace provisioning used a temporary path-specific AppArmor userns profile for
the root-owned pinned bubblewrap binary. Proof code ran as an unprivileged user.
Global userns restrictions were retained; provisioning and cleanup reports are included.

The local result is not Palomar registration, editorial acceptance or a signed tracker
receipt. Maintainers review catalogue status changes before publication. Source-version
and Challenge-import restrictions for Palomar registration still apply.

Reproduction: first follow the immutable proof snapshot's README. Place the retained
verify_candidate.py under WORKSPACE/tightening-research/checkers beside tools matching
tool-pins.json (Palomar sources, source lean4export, judge toolchain and bubblewrap).
Copy checker-binary-pins.json to WORKSPACE/tightening-research/checkers/tool-pins.json;
this is the driver's flat input file. The dossier's separate tool-pins.json records
nested metadata from the accepted run and cannot substitute for that input file.
Provision a disposable Linux worker with genuine nested sandbox support, then run
python3 verify_candidate.py --candidate WORKSPACE/compressed --run-id fresh-check
using --bwrap and, where applicable, the documented temporary profile options.
Do not disable the driver's preflight or any kernel. The driver refuses existing run
directories and audits all native source/object hashes before compiling the wrappers.

Large proof exports are omitted from this website; their actual sizes and SHA256 hashes
are retained and fresh exports can be regenerated. Workspace prefixes in runtime
metadata/logs are neutralized. Source bytes, tool hashes and recorded outcomes remain
unchanged. collection.json authenticates every published file; website checks verify
evidence integrity and do not execute the mathematical checkers.
