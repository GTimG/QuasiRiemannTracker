# Contributing to QRH Bounds

## Add a result or improve the website

1. Fork the repository and create a branch. Edit `catalogue/results.json` to add or correct a result, preserving exact constants, authorship, publication dates and evidence links.
2. Use **verification-pending** for external formalizations not reproduced here. Use **framework-verified** only after the exact claimed statements and their definitions pass Comparator, with exported proofs accepted by Lean, NanoDa and con-ron. Only `propext`, `Classical.choice` and `Quot.sound` are permitted. Retain the source, checker pins, exact statements and acceptance reports for maintainer review. These labels do not create a signed Comparator/NanoDa receipt. Never invent a local verification date.
3. Add proof sources under `proofs/<stable-id>/` with license/attribution and reproduction instructions. Existing proof snapshots are immutable; submit revisions as a new directory. Heavy Lean checks are separate from website CI.
4. Run `npm ci --ignore-scripts`, `npm run check`, and `npm run test:browser` (install Chromium with `npx playwright install chromium` if necessary).
5. Open a pull request describing the result and its evidence. After site checks and maintainer review, merging updates the public website automatically through GitHub Pages.

For an update to the same catalogue contribution, retain its displayed `id` and
point `proof_revision` to the reviewed new proof snapshot. Preserve the previous
metadata in `historical_records`; it remains authenticated but does not create
another chart point. Both revisions' proof archives and checker evidence stay
immutable. Add the explicit revision mapping and its evidence checks when
introducing a revision. This catalogue workflow does not change the separate
signed registry's immutable contribution IDs or supersession rules below.

Liu's existing algebraic constant retains its exact expression and a certified rational enclosure for plotting. The validator checks the enclosure with integer arithmetic; a truncated decimal must not replace the theorem's constant. New algebraic forms need a reviewed exact representation and comparison method.

No author can grant themselves a verified badge merely by passing a website build. Status and evidence changes require maintainer review. The automatic signed admission path below is not running. It must be updated to require all three kernels and tested before it can admit verified results.

For independent reproduction of an existing pending result, use the
[external verification evidence format](docs/EXTERNAL-VERIFICATION.md). It binds
the exact checked source and target to a reviewed immutable dossier, with separate
licensed-archive and remote-source publication modes. It does not alter the
signed admission protocol.
The algebraic endpoint dossier's complete `collection.json` is pinned by
`evidence_collection_sha256` in `core/algebraic-kernel-pins.json`. Its digest
authenticates the exact manifest bytes; the manifest then binds every evidence
file, including the original report, publication transformations and logs. A
contributor cannot replace the reports and recalculate their checksums without
invalidating this pin. Maintainers set or update it only after independent proof
verification and evidence review, with the code-owner review required for `core/`.
Do not regenerate the pin automatically to fix a failing build. Preserve existing
dossiers and introduce later runs as separate evidence. This integrity check
does not rerun Lean or create a signed registry admission.

## Signed Comparator + NanoDa admission (separate, not yet commissioned)

The track admits only the fixed all-Dirichlet theorem. It quantifies over every natural modulus with `NeZero q`, every complex Dirichlet character and every complex `s` with `θ < s.re`, retaining `¬ (χ = 1 ∧ s = 1)` and `_root_.DirichletCharacter.LFunction`. Zeta-only, conditional and restricted-character results do not qualify. A manuscript, a successful Lean build or an AI critic's approval is not admission evidence.

1. Copy `submissions/openai-baseline/` to a new stable lowercase ID. Replace its explanation, author metadata and Lean proof. Keep your modules in `src/Candidate/`; use `Candidate.Main` or another valid module as your entrypoint.
2. Update `manifest.json` following `schemas/submission.schema.json`. Store numerator and denominator as decimal **strings**, with a positive denominator, no leading zeros, and gcd = 1. `14/16` is rejected; use `7/8`. Bounds must be at most `7/8`; equal bounds are welcome as alternative proofs.
3. List all authors accurately, describe the method, include HTTPS references and an appropriate contribution license (Apache-2.0, MIT, BSD-2-Clause, BSD-3-Clause or CC0-1.0). Include `LICENSE` and preserve required notices. Maintainers still review compatibility and attribution; a declared license alone cannot grant rights you do not have.
4. Put only actual mathematical reuse in `builds_on`. IDs must exist in the published registry and predate this verification. Put citations, comparisons and acknowledgments in `references`/explanation instead. Method similarity does not imply dependence.
5. Run `npm run verify -- submissions/your-id --image sha256:APPROVED_LOCAL_IMAGE_ID`. This requires the documented disposable Linux worker and sealed libraries. A local attempt is not a signed public receipt.
6. Open a PR changing **only this submission directory**, using the supplied PR template. No symlinks, binaries, `.olean` files, lakefiles, toolchain changes, caches, workflow changes or registry entries are allowed. Dependencies come from the approved image; request new libraries in a separate infrastructure PR.
7. Opening or updating the PR automatically records it as pending and queues the protected verification workflow once the isolated worker is commissioned. Drafts are listed without execution; an unconfigured worker is shown as awaiting setup. See [automatic intake](docs/AUTOMATIC-SUBMISSIONS.md). It fetches source blobs at the exact head, generates the canonical challenge, isolates checking, then signs a result in a separate job. A head change requires a new run, even if the Lean files look unchanged.
8. A different maintainer reviews attribution and licensing at that exact commit. After merge, the publication job checks that the merged submission content matches the receipt. Archive every successful signed receipt first, using the protected verification journal. Publication uses the earliest valid receipt for that exact revision.

Published IDs and receipts are immutable. New revisions need a new contribution ID; use explicit predecessors and, when appropriate, a signed supersession event. Withdrawals do not delete historical evidence.

The example's mathematical authorship belongs to OpenAI, not to QRH Bounds. The original-terminal-proof example is currently infrastructure-blocked in this stricter admission pipeline. OpenAI’s original proof was checked separately on Linux verification worker with Comparator, Lean, NanoDa and con-ron; its reports are linked in the catalogue.

### Replaying the pinned Liu contribution

Use the [sandboxed maintainer command](verifier/liu/README.md) from a protected,
reviewed checkout. The immutable Liu dossier's earlier native scripts are
historical evidence and must not be used as untrusted-submission entrypoints.
The replacement exports the canonical challenge before candidate code executes,
clears the candidate environment, runs every compilation offline under genuine
Linux confinement, and requires all three independent kernels. A maintainer
must review tool/profile changes separately from proof PRs.
