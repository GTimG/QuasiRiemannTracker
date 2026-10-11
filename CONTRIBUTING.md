# Contributing to QRH Bounds

## Required PR declaration and admission

The workflow classifies each PR from its changed files and assigns the matching
`maintenance` and `new-bound` labels. Maintenance PR bodies contain a summary;
remove the result fields and New bound section from the template. A result PR
starts its body with its stable result ID, exact checked bound and decimal
approximation, for example:

```text
QRH-Result: example-result
QRH-Bound: 4374433/5000000
QRH-Decimal: 0.87488660
```

Use the exact rational or algebraic bound string authenticated by the maintainer
receipt and admission record. Result PRs require the three body fields above
and independent verification evidence.

`QRH-Decimal` is required for new bounds. Supply a truncated decimal written as
`0.` followed by 1–200 digits. Every supplied digit is checked using exact
integer arithmetic (`BigInt`). Include enough digits to differ from the
strongest bound among the current **framework-verified** catalogue records on
the trusted base, truncated to the same precision.
For a frontier of `0.87488664704`, the example above needs at least eight
decimal places: `0.87488660` differs from `0.87488664`, while seven places would
show `0.8748866` for both. Admission requires a value distinct from the current
frontier. An irrational bound keeps its exact expression in `QRH-Bound`; its
decimal is checked against the certified enclosure in the trusted evidence.

Changes under `proofs/`, `public/proofs/`, `submissions/`, `catalogue/` or
`registry/records/`, and changes to `public/catalogue.json` or
`public/registry.json`, receive `new-bound`. This includes deletions, metadata
corrections and either path of a rename. New-bound PRs are confined to those
proof/result paths or Lean files outside `verifier/`, `core/` and `tests/`, which
also require new-bound admission. All other paths receive `maintenance`.
Mixed PRs receive both labels and fail admission. A QRH result declaration or
New bound section requires a PR confined to proof/result changes. Put website,
documentation, workflow, verifier and dependency changes in a separate
maintenance PR. The workflow creates missing managed labels and preserves
unrelated labels. File classification and authenticated evidence determine
admission.

The `qrh/pr-admission` workflow executes trusted default-branch validation code
and reads candidate metadata and changed paths through the GitHub API. For
`new-bound`, admission requires an independent maintainer's accepted check for
this repository, PR number, exact head commit, result ID and exact bound. The
evidence must authenticate Comparator and all three kernels: Lean, NanoDa and
con-ron. Every new commit requires a new admission. Editing the declaration
reruns the check.

## Add a result or improve the website

1. Fork the repository and create a branch. For a result, edit `catalogue/results.json`, preserving exact constants, authorship, publication dates and evidence links. Keep any checking infrastructure changes in a separate PR.
2. Use **framework-verified** after an independent maintainer run in the trusted offline Linux sandbox: the exact claimed statements and their definitions must pass Comparator, with exported proofs accepted by Lean, NanoDa and con-ron. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. The maintainer receipt must bind the complete checked source and dependency pins. Each source revision requires independent verification. Retain the source, checker pins, exact statements and acceptance reports for maintainer review. Use the first successful independent run for the verification date and timeline. Existing **verification-pending** entries describe historical evidence; all new result PRs require admission.
3. Add proof sources under `proofs/<stable-id>/` with license/attribution and reproduction instructions. Existing proof snapshots are immutable; submit revisions as a new directory. Heavy Lean checks run independently of website CI.
4. Run `npm ci --ignore-scripts`, `npm run check`, and `npm run test:browser` (install Chromium with `npx playwright install chromium` if necessary).
5. Open a pull request with a summary; for a result, include the required body declaration, attribution and evidence links. Complete the independent check and admission for the exact PR head. After `qrh/pr-admission`, site checks and maintainer review, merging updates the public website automatically through GitHub Pages.

### Registering an independently checked head

A maintainer runs the appropriate reviewed replay driver on a disposable,
offline Linux worker, then reviews the resulting receipt, complete source
bindings, canonical challenge, checker acceptance and isolation evidence.
Use a replay profile supported by `core/maintainer-replay.mjs`. If a result needs
a new driver, target representation or tool profile, review and merge that
infrastructure first, then perform the independent check.

Publish the immutable replay dossier under `evidence/pr-checks/<id>/` and add
its record to `verifier/pr-admissions.json` in a separate maintainer-reviewed
maintenance PR. An already reviewed dossier under `public/proofs/` may also be
referenced. New dossiers under `evidence/pr-checks/` follow the maintenance
review process. The admissions file has `schema_version: 1` and an `admissions`
array. Each entry specifies `repository`, `number`, `head_sha`, `result_id`,
`theta_exact`, `pin` and `contribution`; the pin and contribution must pass the existing independent
replay validator. The dossier's `reviewed_pr_head` must match `head_sha`.
The `pin` uses the existing replay-pin format (for example,
`core/cycle25-kernel-pins.json`). The `contribution` identifies the checked source
`repository`, `source_commit`, `source_compiler`, `judge_toolchain` and
`palomar_commit`, plus any fields required by that replay profile.
The gate loads these admission records and evidence from the trusted default
branch.

For an irrational exact bound, the checksum-pinned `result.json` must include
a certified `bound_interval` for that same `theta_exact`, with rational
`lower` and `upper` objects containing `numerator` and `denominator`. The gate
reads this report through the existing replay validator. Both interval endpoints
must produce the declared decimal prefix at its supplied precision. If they
disagree, refine the certified enclosure before registering the evidence.

Once that maintenance PR is on the default branch, a maintainer can dispatch
the PR admission workflow with the candidate PR number to check its current
head again. Dispatching preserves the checked head; every new commit requires
a new admission. The admissions file starts empty, and each result PR requires
its own registered acceptance, including existing open PRs.

For an update to the same catalogue contribution, retain its displayed `id` and
point `proof_revision` to the reviewed new proof snapshot. Preserve the previous
metadata in `historical_records` for authentication. The contribution retains
one chart point. Both revisions' proof archives and checker evidence stay
immutable. Add the explicit revision mapping and its evidence checks when
introducing a revision. The signed registry uses immutable contribution IDs and
the supersession rules below.

Liu's existing algebraic constant retains its exact expression and a certified rational enclosure for plotting. The validator checks the enclosure with integer arithmetic and preserves the theorem's exact constant. New algebraic forms need a reviewed exact representation and comparison method.

Status and evidence changes require maintainer review and PR admission. The
independent maintainer replay process above is the active admission path. The
automatic signed service below awaits commissioning, including an update to
require all three kernels and validation of that requirement.

For independent reproduction of an existing pending result, use the
[external verification evidence format](docs/EXTERNAL-VERIFICATION.md). It binds
the exact checked source and target to a reviewed immutable dossier, with separate
licensed-archive and remote-source publication modes.
The algebraic endpoint dossier's complete `collection.json` is pinned by
`evidence_collection_sha256` in `core/algebraic-kernel-pins.json`. Its digest
authenticates the exact manifest bytes; the manifest then binds every evidence
file, including the original report, publication transformations and logs.
Setting or updating the pin requires independent proof verification, evidence
review and code-owner review for `core/`. Preserve existing dossiers and
introduce later runs as separate evidence. Build-time validation authenticates
the retained evidence's integrity;
maintainers perform proof replay on the offline worker.

## Signed Comparator + NanoDa admission (awaiting commissioning)

The following lifecycle describes the signed service after commissioning.
Every submission also requires the active `qrh/pr-admission` check.

The track requires the fixed all-Dirichlet theorem. It quantifies over every natural modulus with `NeZero q`, every complex Dirichlet character and every complex `s` with `θ < s.re`, retaining `¬ (χ = 1 ∧ s = 1)` and `_root_.DirichletCharacter.LFunction`. Admission requires independent verification of this complete statement and its definitions, using the canonical challenge and permitted axioms.

1. Copy `submissions/openai-baseline/` to a new stable lowercase ID. Replace its explanation, author metadata and Lean proof. Keep your modules in `src/Candidate/`; use `Candidate.Main` or another valid module as your entrypoint.
2. Update `manifest.json` following `schemas/submission.schema.json`. Store numerator and denominator as canonical decimal **strings**: the first digit of each nonzero integer is 1–9, the denominator is positive, and gcd = 1. For example, use `7/8`. Bounds must be at most `7/8`; the active PR gate additionally requires a decimal digit differing from the current verified frontier.
3. List all authors accurately, describe the method, include HTTPS references and an appropriate contribution license (Apache-2.0, MIT, BSD-2-Clause, BSD-3-Clause or CC0-1.0). Include `LICENSE` and preserve required notices. Maintainers review attribution, license compatibility and the rights to distribute all contributed material.
4. Document actual mathematical reuse in `builds_on`. IDs must exist in the published registry and predate this verification. Use `references` and the explanation for citations, comparisons and acknowledgments.
5. Run `npm run verify -- submissions/your-id --image sha256:APPROVED_LOCAL_IMAGE_ID` on the documented disposable Linux worker with sealed libraries. The protected workflow creates the signed public receipt after successful verification.
6. Open a PR confined to this submission directory, using the supplied template. Include regular text files: `manifest.json`, `explanation.md`, `LICENSE`, optional `NOTICE`, and Lean modules under `src/Candidate/`. Use the toolchain and dependencies supplied by the approved image; request new libraries in a separate infrastructure PR.
7. A maintainer dispatches the protected verification workflow. It fetches source blobs at the exact head, generates the canonical challenge, isolates checking, then signs a result in a separate job. Every head change requires a new run.
8. A different maintainer reviews attribution and licensing at that exact commit. After merge, the publication job checks that the merged submission content matches the receipt. Archive every successful signed receipt first, using the protected verification journal. Publication uses the earliest valid receipt for that exact revision.

Published IDs and receipts are immutable. New revisions need a new contribution ID; use explicit predecessors and, when appropriate, a signed supersession event. Withdrawals preserve historical evidence.

The example's mathematical authorship belongs to OpenAI. The original-terminal-proof example awaits infrastructure commissioning for the signed admission pipeline. OpenAI’s original proof passed independent checks on a Linux verification worker with Comparator, Lean, NanoDa and con-ron; its reports are linked in the catalogue.

### Replaying the pinned Liu contribution

Use the [sandboxed maintainer command](verifier/liu/README.md) from a protected,
reviewed checkout. The immutable Liu dossier retains the earlier native scripts
as historical evidence. Submit candidate code through the sandboxed maintainer
driver, which exports the canonical challenge before candidate code executes,
clears the candidate environment, runs every compilation offline under genuine
Linux confinement, and requires all three independent kernels. A maintainer
must review tool/profile changes separately from proof PRs.
