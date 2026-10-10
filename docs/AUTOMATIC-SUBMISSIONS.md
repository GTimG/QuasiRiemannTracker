# Automatic submission intake

The `Track pending submissions` workflow records valid proof PRs under
`submissions/<id>` and automatically dispatches the existing isolated verification
workflow once its worker is configured. Website/catalogue PRs are not proof submissions.

## PR lifecycle

1. Opening or updating a PR triggers trusted intake. The workflow checks out only
   its immutable base-repository workflow commit. It reads PR files through the
   GitHub API, applies the existing one-directory/file allowlist, size limits,
   manifest validation, and required source/explanation/license checks. It never
   executes submitted scripts, lakefiles or Lean on the intake runner.
2. Valid metadata is committed to `submission-status/submissions.json` on an
   orphan `submission-status` data branch. Each record binds the PR and exact head
   SHA. Prior revisions remain in the feed and Git history. Draft PRs are recorded
   without starting a verifier. Malformed/mixed infrastructure-and-proof PRs are
   refused; the intake workflow log explains why.
3. If `verifier/trust-policy.json` has no commissioned worker configuration, the
   website shows **Verification pending — Awaiting worker setup**. Once configured,
   intake dispatches `verify-submission.yml` on the default branch with the PR
   number and expected head SHA. The existing protected worker environment still
   applies; dispatch does not bypass required environment approval.
4. The worker re-fetches the PR and refuses closed, draft or changed-head PRs.
   Candidate Lean runs inside the existing offline, unprivileged worker. Signing
   remains in the separate protected job. The signed admission service currently
   checks Comparator + NanoDa; it is not the catalogue's three-kernel verification
   protocol and must be updated and commissioned before use.
5. Trusted verification workflow events refresh the feed using GitHub's run
   metadata, matching the workflow ID, default branch, PR number and exact head.
   No PR-controlled run artifacts are downloaded by intake. The website links
   the run's build/check logs and shows queued/running/failed/cancelled or
   **Checks passed — awaiting review**. Workflow failure is not a claim that the
   mathematical theorem is false.
6. Source changes create a new record; older revisions become superseded. Closed
   PRs are retained in history but hidden from the current pending list. Merged
   submissions remain pending publication until their exact commit appears in
   the authenticated signed registry. A successful job never grants a verified
   badge or changes the best verified bound by itself.

The workflow reconciles all current submissions every 15 minutes and supports
manual dispatch, recovering missed events and retrying failed dispatches. A single
concurrency group serializes writes to the data branch. Pending entries are included in the table and progress chart with amber hollow
markers and check-log links in the shared detail view. The progress line and best bound use
only verified results. Pending and verified results share the same table rows and
detail layout, with verification badges indicating status. The initial plot scale
fits verified results and pending bounds stronger than the best verified bound;
weaker pending results remain in the table.

## Setup

- Merge the intake workflow and website component into the default branch. Its
  first default-branch push creates the public status branch, including an empty
  feed when there are no submissions. The feature cannot run merely by being in
  an unmerged PR.
- Allow its job-scoped token permissions: `contents: write`, `actions: write`,
  and `pull-requests: read`. The Actions token can dispatch another workflow via
  `workflow_dispatch`; no personal access token is needed. This job uses no
  signing secrets and modifies only the separate status data branch. Configure
  branch/ruleset permissions to permit that branch's bot updates while retaining
  the existing source and registry protections.
- Keep the worker, signing, independent review and publication setup in
  [GITHUB.md](GITHUB.md). Provision the disposable Linux runner, sealed image,
  acceptance record and signing keys, and set the reviewed trust policy. The
  current checked-in policy is unconfigured; this change does not commission a
  worker or change mathematical verification requirements.

The browser reads the public feed from `raw.githubusercontent.com`, which supports
CORS and cross-origin resource access. The hosted runner uses authenticated
server-side API requests; browser CORS does not apply there. The UI polls once a
minute; GitHub Raw's CDN may delay visible updates by about five minutes. A missing
status branch is treated as not initialized, while other fetch errors are shown.
There is no website rebuild or merge required for each pending-status update.

GitHub references: [trusted PR-event security](https://docs.github.com/en/actions/reference/security/securely-using-pull_request_target)
and [workflow dispatch with the Actions token](https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/trigger-a-workflow).

## Local preview of open PRs

Build with `VITE_SUBMISSION_STATUS_URL=/preview-submissions.json npm run build`
then run `node scripts/preview-submissions.mjs` (requires authenticated GitHub CLI).
It reads currently open catalogue/proposal PRs and writes their claimed metadata
to `dist/preview-submissions.json`, without running their code. This local override
uses a local snapshot and links the real PRs. Legacy catalogue/proposal PRs
are previewed as awaiting maintainer verification; they are not automatically
eligible for the `submissions/<id>` verifier.
It is not used in normal production builds. Never commit fixture submissions to
the real status branch. Browser tests intercept the feed without publishing data.
