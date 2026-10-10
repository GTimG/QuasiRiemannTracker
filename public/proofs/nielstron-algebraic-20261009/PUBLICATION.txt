# Published source and native evidence

publication-files.json is an explicitly reviewed allowlist. The adjacent
repository manifest and public source archive authenticate exactly those
files. Archives use normalized ownership and timestamps. Case-insensitive
path collisions, symlinks, binaries, caches and operational histories are
rejected. Dependency notices live under compressed/third-party-notices,
so compressed/LICENSE remains portable to case-insensitive filesystems.

Lean source, build scripts, inherited inputs and notices retain their bytes.
Workspace prefixes in runtime metadata/logs are neutralized, with original
and published hashes retained in publication-transformations.json. Original
native reports may retain hashes of omitted compiled objects and original
runtime logs; the transformation record explains every changed published
metadata byte. Reproduction creates new environment-specific native logs.

This source collection remains a historical native-only, verification-pending
snapshot. A future independent checker acceptance must use a new dossier and
bind these source files, their manifest, and an exact public source commit.
It must authenticate the seven fixed targets, positive and negative preflight
controls, Comparator and all three kernels, allowed axioms, pinned tools,
actual raw acceptance logs, and complete sandbox cleanup. Updating catalogue
status requires validating that genuine later evidence. This packager never
changes the catalogue, previous snapshots, or checker evidence.
