# Reproduce the finished Cycle25 proof

This recipe uses ordinary Lean 4.34.1 (compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`), Python 3.9+, Git for local patch
application, and `elan`. No Git remote operation is used. Keep the supplied
lockfile unchanged; do not run `lake update`.

The published proof directory has sibling `formalization/`, `dependencies/`
and `reproduce/` directories. `formalization/` contains exactly the 3,224 Lean
sources in `frozen-source-inventory.json`, plus the three configuration files
supplied here (`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`). Those
sources comprise 298 finished Cycle25 modules, three reused independent moment
modules, and 2,923 pinned OpenAI modules. Files outside this closure are not
required by the endpoint and are excluded from the published source package.

From the proof directory, in a fresh standalone checkout:

```sh
elan toolchain install leanprover/lean4:v4.34.1
python3 reproduce/verify_source.py --project formalization
python3 reproduce/bootstrap_dependencies.py --project formalization --prepare
python3 reproduce/verify_source.py --project formalization --build
```

This command builds third-party dependencies from source and may take
substantially longer than the earlier contributor build. A host C compiler may
be needed by dependency build targets. The final command builds `Cycle25.Assembly.Final.Endpoint` and all of its local
source dependencies. With a fresh project it does not reuse this project's earlier `.olean` files or build unrelated dependency defaults. Use a fresh `formalization/.lake/` to obtain a
fresh local-source build. A successful build establishes ordinary Lean
compilation; three-kernel acceptance and exact-statement comparison have their
own retained evidence and reproduction instructions.

The bootstrap downloads HTTPS source archives at the exact commit IDs in
`dependencies/dependency-pins.json`, checks every needed third-party Lean
source and package configuration against `needed-package-sources.json`, and
applies the two hash-pinned compatibility patches. Lake resolves these prepared
archives as local path dependencies, so it cannot change their Git revisions.
The Git URLs/revisions remain in the separate immutable source lock. A wrong
existing dependency directory is preserved and causes a failure; use a fresh
directory instead of resetting it.

For offline preparation, supply source archives named
`PACKAGE-COMMIT.tar.gz` (for example
`mathlib-d13f23b723b8a846827a245b89c10fc7d3f11612.tar.gz`):

```sh
python3 reproduce/bootstrap_dependencies.py --project formalization --prepare --archive-dir /absolute/path/to/archives
python3 reproduce/bootstrap_dependencies.py --project formalization --check
```

Each archive must have one root directory, as GitHub's commit archives do.
Archive links and special files are refused. Three known, unused documentation
or benchmark symlinks in Mathlib/Batteries are skipped and never materialized;
they are explicitly listed in the source lock.

The minimal PrimeNumberTheoremAnd patch retains the exact four imported Lean
files (`Wiener`, `Fourier`, `SmoothExistence`, `Sobolev`) from the verified
source environment. Its build configuration removes unused supplementary
libraries, default targets, and tooling dependencies. All 15 modified Rellich
modules are imported and retain their earlier patch unchanged. The imported
Lean source bytes match the checking run; these configuration changes are
recorded separately in `dependencies/compatibility-evidence.json`.

The historical clean-001 run compiled 301 Cycle25/reused-moment modules from
frozen source while reusing pinned OAI and third-party compiled libraries.
It was not a full source-only rebuild of the 2,923 OAI modules. The portable
command above rebuilds that OAI closure as well. Packaging validation checks
source identity, pristine-archive preparation, and the 19 compatibility modules;
it does not claim a second full endpoint or three-kernel run under the pruned
configuration.

The pinned Mathlib cache tool rejects local-path entries when comparing them
with its Git manifest (`Cache/Requests.lean`, `checkForManifestMismatch`).
Therefore `lake exe cache get` is not advertised for this path-based recipe.
An existing cache may be useful in a separately reviewed reproduction setup,
but the command above needs no cache service or Git remote synchronization.
