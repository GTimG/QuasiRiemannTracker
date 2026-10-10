# GitHub submission and publication workflow

No remote repository has been configured yet. For ordinary catalogue and website contributions, the ready workflow is PR → site checks → review/merge → automatic Pages deployment; see `DEPLOYMENT.md`. That route does not execute submitted Lean or mint verification receipts.

The remainder describes the separate, stricter signed proof-admission service. Its commissioning is not a prerequisite for publishing the catalogue with native Lean and pending labels.

## Branch and environment protections (required)

- Protect the default branch: no direct pushes, force pushes or deletion; independent maintainer review; dismiss stale approvals; require approval of the most recent push. Prevent administrator/bot bypass for submission admission.
- Populate `.github/CODEOWNERS` with real maintainer/team identities before enabling Actions. Require code-owner review for `.github/`, `verifier/`, `worker/`, `schemas/`, `core/`, lockfiles and all `registry/` paths. Separate infrastructure changes from one-submission PRs.
- Restrict Actions to approved actions pinned by commit and the default read-only token permissions. No secrets for fork PRs. The supplied verification workflow uses **`workflow_dispatch` on the default branch**, triggered automatically by trusted intake or manually by a maintainer, and checks out the immutable `github.workflow_sha`. It never checks out a PR as executable orchestration.
- Require the exact-head verification check produced by the protected signing job (see below) before merge, in addition to code-owner/attribution/license review. Use an organization ruleset requiring this protected workflow or a dedicated check-producing GitHub App if available; do not treat an arbitrary same-name status from PR-controlled CI as authoritative. Signed-record verification still independently gates publication.
- Protect `verification-workers`, `receipt-signing` and `registry-publication` environments: default branch only, required independent maintainers, prevent self-review, no bypass. Configure no secrets in `verification-workers`. Store Ed25519 verification/publication private keys separately in the two signing environments; public keys and permitted IDs go in reviewed policy.
- Provision the `qrh-ephemeral` runner group as JIT/one-job disposable Linux VMs. Never attach a persistent general-purpose self-hosted runner. The worker image is prebuilt, locally available and pinned by actual image ID. Destroy the entire runner after each checking job, including failures. Rootless Docker, kernel support and cgroup limits must be operational and commissioned.
- Keep the append-only registry check mandatory for all registry changes: `node verifier/audit-history.mjs BASE_COMMIT`. Validate signed contents with `npm run build`. `BASE_COMMIT` must be the actual protected base SHA, not a submitted string.

The workflow names alone do not create these repository protections. An administrator must configure them; the local project cannot enforce remote GitHub settings before a repository exists.

## Proof PR lifecycle

1. The contributor opens a PR adding a single `submissions/<id>/` directory. Schema, file count/size, normalized rational, safe paths, file modes and IDs are validated by trusted code. Workflow/library/registry changes are refused.
2. [Trusted intake](AUTOMATIC-SUBMISSIONS.md) records the valid submission as pending and dispatches **Verify submission (trusted dispatch)** with its PR number and expected exact head once the worker is commissioned. Maintainers can also dispatch manually. Trusted API calls fetch raw blobs at its exact 40-character head SHA, not a tarball or submitted lakefile. No candidate script is executed on the runner. Candidate Lean runs only inside the offline unprivileged container, with no host API token or writable cache mounts.
3. On success, a separate hosted runner downloads only the artifact from that same workflow run and attempt. It checks commissioning and current PR head, and signs a receipt using the protected verification key. It posts the exact-head check to the PR commit. Failure or a source change produces no successful receipt. Pending/failure/timeout/blocker logs stay outside the registry.
4. Retain **every successful signed receipt** immediately in the protected journal. Download the signed artifact and run `node verifier/archive-receipt.mjs path/to/receipt.json path/to/verification.log`. Submit these content-addressed files in a separate maintainer journal PR. Archive the first success before accepting a rerun; this prevents the first-verification clock from moving. Keep logs durably in Git/object storage with authenticated digests; GitHub's 90-day artifact retention alone is insufficient.
5. An independent maintainer explicitly reviews attribution, license and explanation and approves the exact head. The latest review per reviewer wins; dismissed or changed reviews revoke approval. Merge only after these checks.
6. Dispatch **Prepare signed publication** with the successful verification run/attempt. It authenticates the Ed25519 receipt, checks the earliest journal receipt, current PR head, independent review and merged source digest. A merge conflict resolution that changes the proof fails the content check and needs a new reviewed submission/receipt.
7. The job creates a signed publication bundle artifact. Put it under `registry/records/<id>/` through a maintainer-reviewed registry PR; run registry authentication/build and immutable-history audit. Deploy the generated static site through the separate approved hosting process.

Publication jobs do not execute Lean, check out candidate sources as code, or grant the worker write access to the repository. They prepare artifacts, not automatic pushes or merges. This avoids giving a submission the ability to publish itself. The separate pending-intake workflow uses `pull_request_target` and verification `workflow_run` events only to read validated data, update the public status branch, and dispatch trusted verification. It checks out only its immutable trusted workflow commit and never executes a PR checkout or downloads candidate artifacts.

## Withdrawals and supersessions

From protected maintainer code with the publication signing key and `QRH_REVIEWER`, run:

```sh
node verifier/events.mjs withdraw existing-id 'Reason for withdrawal'
node verifier/events.mjs supersede old-id 'Reason for supersession' new-id
```

Commit the new signed, chained event through registry review. Never edit/delete the receipt, original publication or historical source. The table can include withdrawn records; the active ranking and frontier respond to events while history retains earlier accepted results.
