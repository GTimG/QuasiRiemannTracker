The QRH development is stored in qrh-20261009/.

Start with audit/FINAL_STATUS.md and formalization/QRH/Nonvanishing.lean.
The full Linux verification worker Lean source, reproduction scripts, pinned dependency/license
records, independent specifications, immutable inputs and compiler logs are
included. The manuscript's author field is unchanged. Site credits identify
Tim Gehrunger as maintainer and ProofCouncil as the project.

Raw Codex conversation/event streams are excluded from this publication copy.
No credential files, installed
compiler, cached third-party checkouts, or compiled oleans are distributed.
The pinned bootstrap obtains compiler and dependency sources for reproduction.

Do not run Lean builds as part of the static website deployment. The native
Lean source checks were performed on Linux verification worker, including a final coordinator
recheck. The separate Comparator + NanoDa admission pipeline is uncommissioned.

qrh-20261009.sha256.json authenticates every published snapshot file. Existing
snapshots should remain immutable; submit new proof revisions in a new directory.
The source archive is under public/proofs/qrh-20261009/source-public.tar.gz with its
SHA256SUMS.txt sidecar. scripts/package-proof.py regenerates the package only
after an explicit reviewed snapshot update; the normal build does not do so.
