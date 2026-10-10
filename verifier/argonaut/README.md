# Sandboxed Argonaut replay

Use this runner and its pins from a **maintainer-reviewed, protected checkout**
on an unprivileged disposable Linux worker. A submission must not control the
runner, pins, profile, tools or canonical library. This is a local mechanical
replay, not a signed registry-admission service.

```sh
/usr/bin/python3 verifier/argonaut/replay.py \
  --profile /srv/qrh/argonaut-worker-profile.json \
  --work /srv/qrh/runs/argonaut-fresh
```

Copy `profile.example.json` to an operator-owned file and configure its three
paths. The work directory must not exist. No credentials, host home directory,
Docker socket, network or shared writable caches are exposed to compilation,
export or judging. Public source/cache downloads happen in separate preparation
phases; archive extraction never executes author Python or Lake scripts.

The worker profile and approved 7,026-module source-built canonical library are
the same ones used by the [Liu replay](../liu/README.md). All binary, source and
compiled-library hashes must match the checked-in pins. The source compiler is
Lean 4.34.1; the independent judge bundle is Lean 4.35.0-rc2 with NanoDa and
con-ron. Palomar is pinned to `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.
The three dependency-provenance files identified by `pins.json.evidence_files`
are available byte-for-byte in the historical Liu dossier. They can also be
reassembled from Argonaut's authenticated metadata chunks. Reproducing the
approved dependency library from an empty cache remains a separate operation.

The runner performs these steps:

1. Authenticate tools and dependencies. Run genuine bubblewrap, cgroup and
   seccomp isolation checks plus matching, mismatched and ill-typed controls.
   Retain the actual control transcripts.
2. Generate the exact fixed `3499999/4000000` challenge and export it before
   loading any candidate code. Only the approved canonical library is visible.
3. Download the exact v0.1.8 release, check its size and SHA-256, and authenticate
   its nested overlay and each of the 152 selected Lean files. No reconstruction
   script or candidate `lakefile.lean` is executed.
4. Authenticate missing dependencies from the official Mathlib cache and extract
   them in the offline sandbox. These cannot supply canonical definitions.
5. Test the actual candidate mounts, then rebuild all 152 selected modules with
   bounded processes, memory and time. Source and dependencies are read-only.
6. Freeze build outputs for solution export. Compare statements and definitions,
   and require acceptance by Lean, NanoDa and con-ron with only `propext`,
   `Classical.choice` and `Quot.sound`. Compiler warnings are retained as
   diagnostics; kernel and axiom checks determine proof acceptance.
7. Write the receipt outside candidate-writable paths, binding the source,
   dependency and tool pins, frozen challenge, proof exports and actual logs.
   Reject diagnostic symlinks, special files and oversized logs before hashing
   or collecting them; a candidate-writable filename is never a trusted path.

The reviewed repository revision is
`5971383edcb0b1cf863927eed3b359d2d3ba346e`. The v0.1.8 tag points to
`193a1ab879f635b8873e4e0d4021884783bed6fb`; the four subsequent commits change
only README/announcement text. The release's source manifest and dependency
pins match Git blobs at the reviewed revision. The exact release SHA-256 is
`37602f9379f833c1b9ad3a6c7c628f961670f4219a9ac0f4190f8eb9b7655a93`.

The existing `public/proofs/argonaut-20261010-kernels` dossier remains immutable.
**Its native build/audit scripts are historical evidence and unsafe entrypoints
for untrusted submissions.** They compiled candidate code with the host
environment before freezing the canonical challenge. Use this runner for the
current verification route; later kernel checks alone do not establish that
the earlier native phases were confined.

Run `python3 tests/argonaut_replay_security.py` for the fast ingestion tests.
They do not replace a real Linux proof replay. `status.json` distinguishes
build failure, mathematical rejection, timeout and infrastructure blockage.
Review raw logs for local paths before publishing; preserve original hashes and
record any path neutralization. Never promote a timed-out or blocked run.

When a successful isolated check is repeated after hardening the collector,
retain both receipts. The catalogue keeps the first successful verification
time, authenticated against the earlier receipt for the same exact source and
checking scope. The current receipt must still match the final runner and pins.
`earlier-acceptance/replay.py` in that evidence package is historical executed
code; it lacks the later diagnostic-collection guards and is not the current
reproduction command.
