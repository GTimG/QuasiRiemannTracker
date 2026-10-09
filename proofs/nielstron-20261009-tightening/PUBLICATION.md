# Published evidence

This snapshot contains the final Lean sources, pinned source-replay tools,
upstream inputs and notices, and selected native build, token, and target-gate
reports. `publication-files.json` is the complete allowlist; the adjacent
`nielstron-20261009-tightening.sha256.json` authenticates every file. The public
`source-public.tar.gz` contains exactly the same allowlisted files, under one
relative root, with normalized archive ownership and timestamps.

Compiled objects, binaries, toolchains, caches, downloaded upstream checkouts,
absolute symlinks, credentials, and private operational records are excluded.
Runtime report/log workspace prefixes are replaced with `/work/qrh-proof`.
`publication-transformations.json` records original and published hashes for
each such metadata change. Lean source, compiler/replay scripts, immutable
input manuscripts, and license notices retain their bytes. Reports retain
hashes of omitted compiler objects as historical run evidence; reproduction
regenerates those objects and its own path-dependent runtime reports.

The public `collection.json` hashes all compact evidence downloads and the
archive, and maps compact copies back to the source snapshot. These checks
authenticate supplied files; they do not rerun Lean or external kernels.
Native Lean verification and a successful source replay are explicitly
distinguished from the still-pending Comparator/NanoDa/con-ron check.

Maintainer packaging uses the existing reviewed allowlist and refuses extra
source files, unexpected downloads, symlinks, and case-insensitive path
collisions. Adding a source file requires an explicit review and allowlist edit;
running the packager never approves it automatically. Dependency notices live
under `compressed/third-party-notices/` so the `compressed/LICENSE` file remains
portable to case-insensitive filesystems.

From the tracker repository root, regenerate the archive and compact downloads
without executing submission code using:

```sh
python3 scripts/package-native-tightening.py --snapshot
npm run check
```
