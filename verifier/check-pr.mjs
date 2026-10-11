// Run this entrypoint from the trusted default-branch checkout.
// Read candidate file paths through the GitHub API.
import { api, pages } from "./github-api.mjs";
import { classifyPRChanges, evaluatePR } from "./pr-admission.mjs";
import { syncPRLabels } from "./pr-labels.mjs";

const repo = process.env.GITHUB_REPOSITORY;
const number = Number(process.env.QRH_PR);
const defaultBranch = process.env.QRH_DEFAULT_BRANCH;
if (
  !/^[\w.-]+\/[\w.-]+$/.test(repo ?? "") ||
  !Number.isSafeInteger(number) ||
  number < 1 ||
  !defaultBranch ||
  process.env.GITHUB_REF !== `refs/heads/${defaultBranch}` ||
  !["pull_request_target", "workflow_dispatch"].includes(
    process.env.GITHUB_EVENT_NAME,
  )
)
  throw Error("Trusted default-branch PR admission orchestration required");

async function writeCheck(route, method, data) {
  const response = await fetch(
    `https://api.github.com/repos/${repo}/${route}`,
    {
      method,
      headers: {
        Accept: "application/vnd.github+json",
        "Content-Type": "application/json",
        "X-GitHub-Api-Version": "2022-11-28",
        Authorization: `Bearer ${process.env.GITHUB_TOKEN}`,
      },
      body: JSON.stringify(data),
    },
  );
  if (!response.ok)
    throw Error(
      `Unable to publish PR admission check: HTTP ${response.status}`,
    );
  return response.json();
}

const pr = await api(`repos/${repo}/pulls/${number}`);
const check = await writeCheck("check-runs", "POST", {
  name: "qrh/pr-admission",
  head_sha: pr.head.sha,
  status: "in_progress",
  details_url: `https://github.com/${repo}/actions/runs/${process.env.GITHUB_RUN_ID}`,
  output: {
    title: "Checking PR declaration and independent proof evidence",
    summary:
      "Classifying changed files and validating declarations against trusted maintainer evidence.",
  },
});
const identity = (p) =>
  JSON.stringify([
    p.number,
    p.state,
    p.draft,
    p.head.sha,
    p.head.repo?.full_name,
    p.base.sha,
    p.base.ref,
    p.base.repo.full_name,
    p.title,
    p.body,
    p.changed_files,
  ]);
let conclusion = "failure",
  summary;
try {
  const files = await pages(`repos/${repo}/pulls/${number}/files`);
  const classification = classifyPRChanges({
    pr,
    files,
    repository: repo,
    defaultBranch,
  });
  await syncPRLabels(repo, number, classification);
  summary = await evaluatePR({
    pr,
    files,
    repository: repo,
    defaultBranch,
    root: process.cwd(),
  });
  const current = await api(`repos/${repo}/pulls/${number}`);
  if (identity(pr) !== identity(current))
    throw Error(
      "PR head, base or declaration changed during validation; rerun admission",
    );
  conclusion = "success";
} catch (error) {
  summary = `Admission failed: ${error.message}\n\nSee CONTRIBUTING.md and docs/GITHUB.md for admission requirements.`;
  process.exitCode = 1;
}
await writeCheck(`check-runs/${check.id}`, "PATCH", {
  status: "completed",
  conclusion,
  completed_at: new Date().toISOString(),
  output: {
    title:
      conclusion === "success"
        ? "PR admission requirements satisfied"
        : "PR admission failed",
    summary,
  },
});
console.log(summary);
