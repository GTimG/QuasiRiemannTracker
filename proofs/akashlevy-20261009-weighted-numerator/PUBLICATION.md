# Published evidence

This snapshot contains the Lean sources and Lake workspace files of the proof,
the three-kernel driver, the manuscript source, the exponent certificate, and
the reports and logs of the recorded checks. `publication-files.json` is the
complete reviewed allowlist; the adjacent
`akashlevy-20261009-weighted-numerator.sha256.json` authenticates every file.
The public `source-public.tar.gz` contains exactly the allowlisted files under
the single root `akashlevy-20261009-weighted-numerator/`, as regular files
with mode 0644, mtime 0, uid/gid 0 and empty owner names.

Included: `formalization/` (`lakefile.toml`, `lean-toolchain`,
`lake-manifest.json`, `setup.sh`, `run_comparator.sh`, the 228 modules of
`WeightedQRH/`, the three `ComparatorChallenges/` modules with their
configurations, `kernels/judge_three_kernels.py`); `manuscript/` (the two TeX
files); `evidence/certificate/` (script and output); `evidence/kernels/` (the
three-kernel report, judge log, Comparator configuration, export targets,
controls with their sources, configuration and logs, Challenge and Solution
sources and logs, tool pins, challenge source audit, and the `lakefile.toml`,
`lake-manifest.json` and build log of the pristine challenge workspace);
`evidence/lake/` (Lake build, rehash and default-kernel Comparator logs);
`evidence/isolated-rebuild/` and `evidence/comparator/` (the earlier route,
with the negative control's challenge and configuration);
`evidence/source-scan.txt`; license and notice files.

Excluded: compiled objects (`.olean`, `.ilean`, `.c`), the Challenge and
Solution exports (382347462 and 1772535340 bytes; their SHA-256 values are in
`evidence/kernels/result.json`), the controls' exports and objects, the
judge's scratch home and temporary directories, compiler and kernel binaries,
toolchains, `.lake` directories, caches, upstream checkouts (`math/`),
credentials, and private operational records. The manuscript PDF is published
only beside the snapshot, in `public/proofs/akashlevy-20261009-weighted-numerator/`.

## Path neutralisation

Runtime logs and JSON reports recorded absolute paths of the author's machine.
In those files only, each such prefix was replaced (longest first) by a
neutral prefix:

| Published prefix | Stood for |
| --- | --- |
| `/work/qrh-proof/formalization` | the scratch Lake workspace that is this package's `formalization/` |
| `/work/qrh-proof/pristine` | the scratch Lake workspace of `evidence/kernels/pristine-workspace/` (pristine openai/math `fd4aeeb2e`) |
| `/work/qrh-proof/kernels` | the output directory of the three-kernel run |
| `/work/qrh-proof/tracker` | the local tracker checkout |
| `/work/qrh-proof/development` | the author's development directory (WeightedQRH sources, isolated rebuild) |
| `/work/qrh-proof/tools/lean-4.35.0-rc2-darwin_aarch64` | the unpacked official Lean v4.35.0-rc2 darwin_aarch64 release |
| `/work/qrh-proof/tools` | the author's tools directory (Comparator and lean4export builds, Landrun stand-in) |
| `/work/qrh-proof/workspace` | the original Lake workspace of the development (pinned dependency builds, fork checkout) |
| `/work/qrh-proof/project` | the author's project directory |
| `/work/qrh-proof/tools/lean-4.34.1` | the elan Lean 4.34.1 toolchain |
| `/work/qrh-proof/home` | the author's home directory |
| `/work/qrh-proof/tmp` | other temporary session directories |

`publication-transformations.json` lists every changed file with its original
and published SHA-256 and the number of replacements per prefix. Hashes
recorded inside the reports (for example the `artifacts` of
`evidence/kernels/result.json`) refer to the original bytes; the validator
checks them against the recorded original hashes.

One script was changed for publication, and is listed there too: line 12 of
`evidence/isolated-rebuild/run_comparator.sh` hard-coded the author's local
tools directory and now reads the required environment variable `QRH_TOOLS`.
No other byte of it changed; the recorded runs in `evidence/comparator/` used
the original script. All other Lean sources, scripts, TeX files and license
texts keep their original bytes. Apart from that line, the isolated-rebuild
scripts are kept as run: they assume the author's original directory layout (sibling
`formalize_11_12/` directories) and prebuilt objects at machine-specific
locations, and need overrides such as `--source-checkout`, `OBJROOT` and
`QRH_TOOLS`, or edits, before they can be rerun.

## Allowlist, manifest and regeneration

The allowlist is reviewed by hand. The tracker check
`python3 scripts/check-akashlevy-publication.py` (run by `npm run check`)
verifies that the files on disk equal the allowlist, that every file matches
the manifest, scans every file for private metadata, and authenticates the
public downloads, the archive, `SHA256SUMS.txt` and `collection.json`. It also
binds the recorded three-kernel report to the catalogue record. It never runs
Lean, Lake, Comparator or a kernel.

From the tracker repository root, the derived files (the manifest, the public
copies of snapshot files, `source-sha256.json`, `source-public.tar.gz`,
`SHA256SUMS.txt` and `collection.json`) are regenerated from this snapshot,
without approving any new file, with:

```sh
python3 scripts/check-akashlevy-publication.py --regenerate
python3 scripts/check-akashlevy-publication.py
npm run check
```
