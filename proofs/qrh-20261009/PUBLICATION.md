# Published proof snapshot

The Lean sources, independent theorem statements, accepted manuscript, retained research inputs, dependency pins, licenses, proof-source hashes and recorded checker outcomes are unchanged.

Compiler logs and environment metadata are **sanitized derivatives** of the original verification records. Internal workspace paths use `/work/qrh-proof` or `/work/qrh-checker`; worker names use `verification-worker`. This changes the bytes and checksums of those logs, not the mathematical proof. The original mathematical checks were not rerun for this publication cleanup, and the sanitized files are not newly signed verification receipts.

Operational handoffs, agent sessions, login/preflight records, progress journals and resource-management notes are not part of the public snapshot. The input checksum list covers the six retained research inputs; older verification reports may describe the original eight-file handoff. Its two operational documents are intentionally omitted. Original evidence is retained privately by the maintainer.

`publication-files.json` is the reviewed path allowlist. Packaging fails if an additional file appears, a file disappears, a symlink is introduced or a privacy check fails. `../qrh-20261009.sha256.json` authenticates the published bytes. Changes to the allowlist and package must receive maintainer review. The download is `source-public.tar.gz`; the previous archive name is no longer published.

Reproduction scripts use a fresh local workspace. The optional Palomar scripts read `QRH_PROOF_ROOT` and `QRH_CHECKER_ROOT` from the operator's environment and require Linux. Keep raw run records private until they have been reviewed and sanitized for publication.
