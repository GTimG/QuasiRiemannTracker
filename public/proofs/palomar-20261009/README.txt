Local verification with Palomar's mechanical checker — 9 October 2026

Both the ProofCouncil exact 874957019421/1000000000000 result and the original
OpenAI 7/8 proof passed Comparator, Lean's fresh-kernel replay, NanoDa and con-ron.
Each check includes the all-Dirichlet, zeta and finite-order Eisenstein Hecke targets.
Only propext, Classical.choice and Quot.sound are permitted; no definition holes
are configured. Challenge and Solution sources make the quantifiers and pole
exclusions directly inspectable. Palomar's positive, mismatched-statement and
ill-typed-proof preflight passed before each run.

This uses PalomarSubmission's unmodified checker/sandbox functions at
 d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44
https://github.com/PalomarRegistry/PalomarSubmission/tree/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44
on Linux verification worker, with task-specific stricter resource ceilings and system bubblewrap.
The source compiler remains Lean 4.34.1. Its matching lean4export at
076e8e57707e813375e8f9da8bf989799ace9680 produced the exports. The actual judge and
all three kernels are from the official Lean 4.35.0-rc2 release, Palomar's current
minimum. Cross-version export compatibility was established by the successful
checks. Tool binaries and release archive are pinned by SHA256 in tool-pins.json.
No accepted manuscript, proof source or dependency pin was changed.
The tool-pins files preserve preparation-time status; result.json and the two
check-status files record the subsequent successful checks.

These are local mechanical checks. They are not Palomar registration or editorial
review. Current Palomar submission requirements additionally include its source
compiler floor, source-module conventions, public repository and metadata rules.
The Hecke statement uses original OpenAI definitions outside its current Challenge
import allowlist. The website's separate signed admission service is not commissioned.

The original 7/8 proof was compiled from pinned OpenAI/math
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, with 20 additional modules in a private
cache; its exported proof was checked directly. Earlier native evidence for 7/8
was a corollary of the stronger ProofCouncil theorem. Historical first-check dates
are retained; the new completion timestamps are in the two check-status JSON files.

collection.json authenticates the retained reports, configs, source wrappers and
logs. The two large proof exports remain on Linux verification worker; their SHA256 digests are in
each result.json. The accepted proof source archive and source-build audit are
separately retained under proofs/qrh-20261009. A website build checks evidence
integrity and does not rerun the mathematical kernels.

Publication format: internal paths and worker identities have been replaced with
neutral placeholders. These logs and reports are sanitized derivatives, not a
new verification run. collection.json and the artifact digests describe the
published bytes; mathematical sources, tool hashes, proof-export hashes and
recorded kernel outcomes are unchanged. See proofs/qrh-20261009/PUBLICATION.md.
For reproduction, set QRH_PROOF_ROOT and QRH_CHECKER_ROOT to dedicated local
Linux directories before invoking the retained scripts.
