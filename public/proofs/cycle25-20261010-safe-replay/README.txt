# Independent quartic-bound replay

The maintainer independently checked Hailey Collet's PR #9 at
`58344dfdbe756cf2f743da1908ffe0582418cf5b` using the protected tracker base
`0f78cd9b99ba745c7b475f76a971d6107229906b`. The run accepted all eight targets
on 10 October 2026 at 16:09:09 UTC. Comparator checked statement and definition
identity; Lean, NanoDa and con-ron accepted the proof closures using only
`propext`, `Classical.choice` and `Quot.sound`.

The main all-Dirichlet challenge is the canonical OpenAI statement with only
`7/8` replaced by `683505193/781250000`. Additional targets cover zeta and the
original Eisenstein Hecke family, their exact quartic endpoints, existence and
uniqueness of the quartic root, and the reusable moment theorem with its stated
smoothness, arithmetic, κ and β conditions. The moment theorem does not require
an additional analytic estimate as a premise.

## Safe reproduction

Use this reviewed runner and its pins from a protected maintainer checkout on
a disposable, unprivileged Linux worker. Do not run the submitted Lakefile,
bootstrap scripts, historical author runner or bare Lean compilation on your
workstation. Lean elaboration is arbitrary code execution. The immutable
contributor archive includes its original instructions and reports as historical
material; those instructions are not the sandboxed verification procedure.

Prepare the exact source bundle by reading immutable Git blobs as data:

```sh
python3 verifier/cycle25/prepare-source.py \
  --tracker /srv/qrh/tracker --output /srv/qrh/cycle25-source.zip
```

The tracker checkout must contain the exact PR revision above. The preparer
checks all 3,609 submitted package files, then produces the byte-identical
3,224-module bundle used by the independent run. It executes no submitted code.
Configure the operator-owned `profile.example.json` with the approved baseline,
checker bundle, dependency provenance and this source bundle. Then run:

```sh
/usr/bin/python3 verifier/cycle25/replay.py \
  --profile /srv/qrh/cycle25-worker-profile.json \
  --work /srv/qrh/runs/cycle25-fresh
```

The source compiler is Lean 4.34.1 at
`5045d0056413266e57c625dcd7c365b10e377c52`; the judge uses Lean 4.35.0-rc2,
Comparator, NanoDa and con-ron through Palomar
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`. The exact binary hashes, dependency
revisions and source inventories are in `pins.json`. Approved library and checker
setup are documented in [the Liu replay instructions](../liu/README.md).
The profile's evidence directory must contain the three provenance files named
by `pins.json.evidence_files`. Missing prerequisites fail closed.

This reuses the separately approved 7,026-module canonical library and pinned
official dependency cache. It is not a cache-free bootstrap. All 298 Cycle25,
three reused moment and 2,923 pinned OpenAI modules are rebuilt with eight bounded
workers. OpenAI sources match `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

The runner tests real bubblewrap/cgroup/seccomp confinement and matching,
mismatched and ill-typed checker controls before candidate execution. It exports
and freezes the trusted challenge first. Compilation and checking have no
network, host home, credentials, sockets or shared writable caches. Sources and
dependencies are read-only. Receipt creation occurs outside candidate-writable
paths; it binds source bytes, tool and dependency pins, exact targets and logs.

## Publication and updates

The site authenticates the protected receipt and every current submission file.
Changing source bytes invalidates acceptance even if archive checksums are
regenerated. Contributor JSON, successful compilation and author reports cannot
grant verified status. The original author evidence remains immutable and
pending; the separate maintainer dossier records independent acceptance.

The chart uses the first independent verification time, not the discovery or
submission date. Submission, publication and merge times are separate; future
publication and merge times remain unset until those events occur.

Large proof exports remain in the retained verification run, with their hashes
in the public receipt. Empty module logs share one public empty log; every
original log hash remains bound by the receipt. Any local path neutralization is
recorded separately. The receipt, statements and kernel verdicts are unchanged.
This is a maintainer mechanical replay, not signed registry admission or a
production submission service.

Run `python3 tests/cycle25_replay_security.py` for ingestion/contract controls
and `node --test tests/cycle25-kernel-evidence.test.mjs` for receipt and source
binding tests. These fast checks do not replace the completed Linux proof run.
Verifier, dependency or tool updates require separate maintainer review and a
fresh isolation/control/proof run. PR code must not control the protected runner.
