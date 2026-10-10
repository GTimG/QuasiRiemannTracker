import { manifest } from "./manifest.mjs";
import { allowedChanges, materialize } from "./github.mjs";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";

export const STATUS_BRANCH = "submission-status";
export const VERIFICATION_WORKFLOW = "verify-submission.yml";

export async function request(route, { method = "GET", body } = {}) {
  const response = await fetch(`https://api.github.com/${route}`, {
    method,
    headers: {
      Accept: "application/vnd.github+json",
      "X-GitHub-Api-Version": "2022-11-28",
      Authorization: `Bearer ${process.env.GITHUB_TOKEN}`,
      "Content-Type": "application/json",
    },
    body: body === undefined ? undefined : JSON.stringify(body),
  });
  if (response.status === 404 && method === "GET") return null;
  if (!response.ok) throw Error(`GitHub API ${response.status}: ${route}`);
  return response.status === 204 ? null : response.json();
}

async function list(api, route) {
  const rows = [];
  for (let page = 1; page <= 100; page++) {
    const result = await api(
      `${route}${route.includes("?") ? "&" : "?"}per_page=100&page=${page}`,
    );
    if (!Array.isArray(result)) throw Error("Unexpected GitHub listing");
    rows.push(...result);
    if (result.length < 100) return rows;
  }
  throw Error("GitHub pagination limit exceeded");
}

async function loadSubmission(pr, id) {
  const dir = mkdtempSync(path.join(tmpdir(), "qrh-intake-"));
  try {
    return (await materialize(pr.head.repo.full_name, pr.head.sha, id, dir))
      .manifest;
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

export function workerConfigured(policy, repo) {
  return (
    policy.repository === repo &&
    /^sha256:[a-f0-9]{64}$/.test(policy.worker_image ?? "") &&
    /^[a-f0-9]{64}$/.test(policy.acceptance_receipt_sha256 ?? "") &&
    Object.keys(policy.verification_keys).length > 0
  );
}

// These are workflow states, never mathematical acceptance or registry admission.
export function verificationState(run) {
  if (run.status !== "completed")
    return run.status === "queued" ? "queued" : "running";
  if (run.conclusion === "success") return "checks-passed";
  if (run.conclusion === "cancelled") return "cancelled";
  return "checks-failed";
}

export async function synchronizeSubmissions({
  repo,
  defaultBranch,
  policy,
  api = request,
  load = loadSubmission,
  now = new Date().toISOString(),
}) {
  if (!/^[\w.-]+\/[\w.-]+$/.test(repo)) throw Error("Invalid repository");
  const prefix = `repos/${repo}`;
  const stored = await api(
    `${prefix}/contents/submissions.json?ref=${STATUS_BRANCH}`,
  );
  const feed = stored
    ? JSON.parse(Buffer.from(stored.content, "base64").toString())
    : { schema_version: 1, repository: repo, records: [] };
  if (
    feed.schema_version !== 1 ||
    feed.repository !== repo ||
    !Array.isArray(feed.records)
  )
    throw Error("Invalid submission status feed");
  const previous = JSON.stringify(feed);
  const open = (await list(api, `${prefix}/pulls?state=open`)).filter(
    (pr) => pr.base.ref === defaultBranch && pr.base.repo.full_name === repo,
  );
  const active = new Set();
  const dispatches = [];
  for (const pr of open) {
    const existing = feed.records.find(
      (r) => r.pr === pr.number && r.head_sha === pr.head.sha,
    );
    let record = existing;
    if (!record) {
      const files = await list(api, `${prefix}/pulls/${pr.number}/files`);
      if (!files.some((f) => f.filename.startsWith("submissions/"))) continue;
      let submission;
      try {
        const id = allowedChanges(files);
        submission = manifest(await load(pr, id));
        if (submission.id !== id)
          throw Error("Manifest ID does not match directory");
      } catch (error) {
        // A malformed or mixed infrastructure/proof PR is not eligible for execution.
        console.error(`PR ${pr.number}: ${error.message}`);
        continue;
      }
      // Bind metadata to its fetched head; do not dispatch a revision that changed meanwhile.
      const current = await api(`${prefix}/pulls/${pr.number}`);
      if (current.head.sha !== pr.head.sha || current.state !== "open")
        continue;
      record = {
        pr: pr.number,
        head_sha: pr.head.sha,
        id: submission.id,
        title: submission.title,
        authors: submission.authors,
        theta: submission.theta,
        method: submission.method,
        entrypoint: submission.entrypoint,
        license: submission.license,
        builds_on: submission.builds_on,
        references: submission.references,
        head_repository: pr.head.repo.full_name,
        submitted_at: pr.created_at,
        recorded_at: now,
        state: "awaiting-worker",
        run_id: null,
        run_attempt: null,
        run_url: null,
      };
      feed.records.push(record);
    }
    active.add(`${pr.number}:${pr.head.sha}`);
    if (["closed", "merged", "superseded"].includes(record.state))
      record.state = "awaiting-worker";
    if (pr.draft) record.state = "draft";
    else if (
      ["draft", "awaiting-worker", "dispatch-failed"].includes(record.state)
    ) {
      record.state = workerConfigured(policy, repo)
        ? "queued"
        : "awaiting-worker";
      if (record.state === "queued") dispatches.push(record);
    }
  }
  // Retain history for prior heads and closed PRs; only current submissions are displayed.
  for (const record of feed.records) {
    if (active.has(`${record.pr}:${record.head_sha}`)) continue;
    if (open.some((pr) => pr.number === record.pr)) record.state = "superseded";
    else if (!["closed", "merged"].includes(record.state)) {
      const pr = await api(`${prefix}/pulls/${record.pr}`);
      record.state =
        pr.head.sha !== record.head_sha
          ? "superseded"
          : pr.merged_at
            ? "merged"
            : "closed";
    }
  }
  if (feed.records.length) {
    const workflow = await api(
      `${prefix}/actions/workflows/${VERIFICATION_WORKFLOW}`,
    );
    if (workflow) {
      const response = await api(
        `${prefix}/actions/workflows/${workflow.id}/runs?event=workflow_dispatch&per_page=100`,
      );
      for (const record of feed.records) {
        if (["draft", "closed", "superseded", "merged"].includes(record.state))
          continue;
        const run = response.workflow_runs.find(
          (run) =>
            run.workflow_id === workflow.id &&
            run.head_branch === defaultBranch &&
            run.event === "workflow_dispatch" &&
            run.display_title ===
              `Verify PR ${record.pr} at ${record.head_sha}`,
        );
        if (!run) continue;
        record.state = verificationState(run);
        record.run_id = run.id;
        record.run_attempt = run.run_attempt;
        record.run_url = `https://github.com/${repo}/actions/runs/${run.id}`;
      }
    }
  }
  for (const record of dispatches) {
    if (record.run_id) continue;
    try {
      await api(
        `${prefix}/actions/workflows/${VERIFICATION_WORKFLOW}/dispatches`,
        {
          method: "POST",
          body: {
            ref: defaultBranch,
            inputs: { pr: String(record.pr), head_sha: record.head_sha },
          },
        },
      );
    } catch (error) {
      record.state = "dispatch-failed";
      console.error(`PR ${record.pr}: ${error.message}`);
    }
  }
  if (stored && JSON.stringify(feed) === previous) return feed;
  feed.updated_at = now;
  await writeFeed(api, prefix, feed, stored);
  return feed;
}

async function writeFeed(api, prefix, feed, stored) {
  const content = JSON.stringify(feed, null, 2) + "\n";
  if (stored) {
    await api(`${prefix}/contents/submissions.json`, {
      method: "PUT",
      body: {
        branch: STATUS_BRANCH,
        message: "Update pending submission status",
        sha: stored.sha,
        content: Buffer.from(content).toString("base64"),
      },
    });
  } else {
    // An orphan data branch keeps pending metadata outside the reviewed source/registry.
    const blob = await api(`${prefix}/git/blobs`, {
      method: "POST",
      body: { content, encoding: "utf-8" },
    });
    const tree = await api(`${prefix}/git/trees`, {
      method: "POST",
      body: {
        tree: [
          {
            path: "submissions.json",
            mode: "100644",
            type: "blob",
            sha: blob.sha,
          },
        ],
      },
    });
    const commit = await api(`${prefix}/git/commits`, {
      method: "POST",
      body: {
        message: "Initialize pending submissions",
        tree: tree.sha,
        parents: [],
      },
    });
    await api(`${prefix}/git/refs`, {
      method: "POST",
      body: { ref: `refs/heads/${STATUS_BRANCH}`, sha: commit.sha },
    });
  }
}
