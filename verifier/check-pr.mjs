// Run this entrypoint from the trusted default-branch checkout.
// Read candidate file paths as data from the API or immutable Git commits.
import { mkdirSync, writeFileSync, appendFileSync } from "node:fs";
import { api } from "./github-api.mjs";
import { prFiles } from "./pr-files.mjs";
import {
  classifyPRChanges,
  evaluatePR,
  parseDeclaration,
} from "./pr-admission.mjs";
import { readSubmissionMetadata } from "./submission-metadata.mjs";
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
    title: "Checking PR declaration and proof",
    summary:
      "Classifying changed files and preparing verification of the submitted proof.",
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
class VerificationRequired extends Error {
  constructor(expected) {
    super("Proof verification is queued");
    this.expected = Array.isArray(expected) ? expected : [expected];
  }
}
let queued = false;
let conclusion = "failure",
  summary;
try {
  const files = await prFiles(pr, repo);
  const classification = classifyPRChanges({
    pr,
    files,
    repository: repo,
    defaultBranch,
  });
  await syncPRLabels(repo, number, classification);
  const declaration = parseDeclaration(pr.body);
  if (declaration)
    await readSubmissionMetadata(api, {
      repository: repo,
      head_sha: pr.head.sha,
      result_id: declaration.result_id,
    });
  summary = await evaluatePR({
    pr,
    files,
    repository: repo,
    defaultBranch,
    root: process.cwd(),
    ...(process.env.QRH_PHASE === "prepare"
      ? {
          validateProofs: (_root, expected) => {
            throw new VerificationRequired(expected);
          },
          validateEvidence: (_root, expected) => {
            throw new VerificationRequired(expected);
          },
        }
      : {}),
  });
  const current = await api(`repos/${repo}/pulls/${number}`);
  if (identity(pr) !== identity(current))
    throw Error(
      "PR head, base or declaration changed during validation; rerun admission",
    );
  conclusion = "success";
} catch (error) {
  if (error instanceof VerificationRequired) {
    queued = true;
    mkdirSync("verification-context", { recursive: true });
    writeFileSync(
      "verification-context/context.json",
      JSON.stringify(
        {
          expected: error.expected[0],
          expectations: error.expected,
          pr,
          check_id: check.id,
          repository: repo,
          defaultBranch,
          run_id: process.env.GITHUB_RUN_ID,
          run_attempt: process.env.GITHUB_RUN_ATTEMPT,
          workflow_sha: process.env.GITHUB_WORKFLOW_SHA,
        },
        null,
        2,
      ) + "\n",
    );
    appendFileSync(
      process.env.GITHUB_OUTPUT,
      `verify=true\nmatrix=${JSON.stringify(error.expected.map((e) => e.result_id))}\n`,
    );
    summary = "Checking the submitted proof in an isolated worker.";
  } else {
    summary = `Admission failed: ${error.message}`;
    process.exitCode = 1;
  }
}
if (!queued)
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
