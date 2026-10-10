# Sandboxed Liu replay

Run `replay.py` from a **maintainer-reviewed, protected checkout** on an
unprivileged disposable Linux worker. The candidate PR must not supply the
runner, pins, profile, tools, or canonical library. This is a bounded local
replay, not a production submission service or signed registry admission.

```sh
/usr/bin/python3 verifier/liu/replay.py \
  --profile /srv/qrh/liu-worker-profile.json \
  --work /srv/qrh/runs/liu-fresh
```

Copy `profile.example.json` to the operator-owned profile and set its three
paths. The work directory must not exist. Do not give the worker credentials,
a Docker socket, secrets, or shared writable caches. Do not run this from a
privileged PR workflow. Preparation may fetch public inputs; compilation,
archive extraction, export and judging have no network access.

The profile locates an **already approved** baseline build, not an arbitrary
Lake cache. Its `audit/final-source-graph.json`, pinned source trees and
`build/source` objects must exactly match `pins.json` and
`approved-library-manifest.json`. Those manifests authenticate the 7,026
source-built dependency modules reused by the independently checked PR #2 run.
The driver copies them into a private directory and mounts them read-only.
It fails closed if anything is missing or changed. Provisioning an equivalent
baseline from an empty cache is a separate operation; this command does not
claim to perform or validate that bootstrap.

The checker layout is `checkers/tools/{palomar,lean4export,lean-4.35.0-rc2-linux}`.
The source compiler lives at `baseline/toolchains/lean-4.34.1-linux`.
`pins.json` records actual SHA256 values for the compiler, exporter, all kernels,
leantar, bubblewrap and the system Python/touch binaries of the tested Linux
profile. Reproducing on a different system needs a separately reviewed tool
profile update; silently repinning binaries is prohibited. Palomar is pinned to
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`; its genuine bubblewrap, cgroup and
seccomp requirements must pass the live positive/negative controls.

The sequence is mandatory:

1. Authenticate tools and the canonical library; run isolation and checker controls.
2. Generate and export the fixed algebraic challenge using only that library.
3. Fetch the pinned author revision as data. Check every selected source hash,
   reconstruct import paths, and authenticate the OAI foundation against Git
   objects. Never import `verify.py`, run `lakefile.lean`, or execute author scripts.
4. Fetch missing dependency archives from the official Mathlib cache using
   reviewed hashes and matching source hashes. Extract them inside a sandbox.
   They cannot supply the canonical challenge's definitions.
5. Compile all 238 selected modules in the offline sandbox. Freeze build outputs
   read-only for solution compilation and export.
6. Compare the fixed all-Dirichlet, zeta and Hecke targets and their definitions,
   permit only `propext`, `Classical.choice` and `Quot.sound`, and require Lean,
   NanoDa and con-ron acceptance. Write the receipt outside candidate mounts.

`result.json` binds the source revision/content, driver/pins, generated statement,
exports, toolchain, kernels and logs. Candidate-generated build output is never
accepted as a verification receipt. `status.json` distinguishes a failed build,
checker rejection, timeout and infrastructure failure. Raw output contains local
paths; review and neutralize it before publishing. Do not redistribute Liu's
sources or exported proof streams without a license grant.

The immutable `public/proofs/liu-20261010-kernels` collection records the
contributor's earlier run. **Its historical `reproduce.py`, `build_native.py`
and `verify_native.py` are not safe entrypoints for untrusted submissions.**
They remain byte-for-byte intact to preserve the evidence hashes. Use the
command above; the old native path inherited the host environment and executed
author Python while reading `EXPECTED`. A successful historical replay did not
establish confinement of those earlier native phases.

Run the fast ingestion regressions with `python3 tests/liu_replay_security.py`.
They are distinct from the real Linux integration replay and never stand in for
kernel acceptance or actual sandbox controls.
