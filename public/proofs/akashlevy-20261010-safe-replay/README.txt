# Independent weighted-numerator replay

This maintainer runner checks Akash Levy's exact `10499/12000` all-Dirichlet,
zeta and Eisenstein Hecke statements. Run the reviewed verifier from a protected
checkout on an unprivileged Linux worker. Submission code must never control
the runner, pins, profile, checker tools or canonical library.

The submitted package is pinned to tracker commit
`ec626ec9c0e7ab7b29f6c916314932caeb4df39a`; the reviewed PR head is
`2fd60c0926b66ea18d7436f5ed55250fd006ab5d`. Its dependency fork is
`akashlevy/math` at `c388e88e6519d139ad2ca5571ef0c7fbf0e245b5`.
The trusted tracker base is `c4806753858945a008a92c564130809548e8c4bb`.
No submitted Lakefile, setup script or author-side judge is executed.

## Reproduction

Prepare a source bundle from checkouts containing those exact Git objects:

```sh
python3 verifier/akashlevy/prepare-source.py \
  --tracker /srv/qrh/tracker --fork /srv/qrh/akashlevy-math \
  --output /srv/qrh/akashlevy-source.zip
```

This reads Git blobs as data and authenticates all 302 submitted package files,
all 228 new Lean modules and the required 2,670 dependency-fork modules against
the reviewed pins. It does not rely on the checkout's current branch or build
objects. Use a fresh output path.

Configure `profile.example.json` with the operator-owned source bundle,
approved baseline library, checker bundle and dependency-provenance paths.
Then the local verification command is:

```sh
/usr/bin/python3 verifier/akashlevy/replay.py \
  --profile /srv/qrh/akashlevy-worker-profile.json \
  --work /srv/qrh/runs/akashlevy-fresh
```

The source compiler is Lean 4.34.1. The judge is Lean 4.35.0-rc2 with Comparator,
NanoDa and con-ron, driven by Palomar revision
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`. Tool hashes and the separately
approved 7,026-module source-built library are the ones used by the earlier
Liu and Argonaut replays. This is not a cache-free bootstrap: follow
`verifier/liu/README.md` for provenance of that approved library. The three
metadata files named by `pins.json.evidence_files` accompany that evidence.
An optional operator-owned `official_cache` directory can supply raw official
cache archives; every archive is hashed and copied into this run before use.
No shared writable cache is mounted into checking processes.

## Checking and trust boundary

The runner first tests real bubblewrap, cgroup and seccomp confinement and runs
matching, mismatched and ill-typed checker controls. It generates the challenge
from maintainer code and exports it using only the approved canonical library
before loading candidate sources. Only the rational replaces the upstream
`7/8`; the all-positive-moduli, all-character statement and pole exclusion are
unchanged.

All 2,898 candidate/dependency-fork modules are rebuilt with eight bounded
workers. Compilers, exporters and the judge have no network, host credentials,
host home, Docker socket or shared writable cache. Source and dependencies are
read-only, the canonical challenge is unavailable to candidate compilation,
and exported proof checking uses frozen build inputs. Permitted axioms are
only `propext`, `Classical.choice` and `Quot.sound`.

The controller writes its receipt outside candidate-writable paths. It binds
the complete source bundle and source manifest, all submitted package files,
exact bound, revisions, dependency and tool pins, driver, frozen challenge,
proof exports and actual logs. The website separately checks these bindings
against the current package. Regenerating publication checksums after a source
change cannot reuse a previous acceptance. Checker crashes, timeouts and
infrastructure failures cannot grant verified status.

The original macOS report remains immutable historical evidence. Its disabled
sandbox and author-controlled setup do not provide independent acceptance.
The new dossier is a maintainer mechanical check, not signed registry admission
or a production submission service. Large proof exports stay private; their
hashes remain in the receipt. Published path neutralization is recorded without
changing Lean source, proof statements or kernel verdicts.

Run `python3 tests/akashlevy_replay_security.py` for ingestion/contract checks.
They do not replace the real Linux replay. Dependency updates require separate
maintainer review, new pins and fresh isolation, negative-control and proof
checks before publication.

Identical empty compiler logs share `logs/empty-module.log` in the public
dossier. `collection.json` maps every original module log to its published
bytes, and the unchanged receipt retains every original hash. Nonempty logs
and the complete raw collection are retained separately.
