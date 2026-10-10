import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { synchronizeSubmissions } from "../verifier/submission-status.mjs";

const repo = "owner/qrh";
const head = "a".repeat(40);
const candidate = {
  ...JSON.parse(
    readFileSync("submissions/openai-baseline/manifest.json", "utf8"),
  ),
  id: "new-proof",
  title: "A submitted proof",
};
const commissioned = {
  repository: repo,
  worker_image: "sha256:" + "b".repeat(64),
  acceptance_receipt_sha256: "c".repeat(64),
  verification_keys: { key: "public-key" },
};
const makePR = () => ({
  number: 7,
  state: "open",
  draft: false,
  created_at: "2026-10-10T10:00:00Z",
  merged_at: null,
  base: { ref: "main", repo: { full_name: repo } },
  head: { sha: head, repo: { full_name: "contributor/qrh" } },
});
function fixture(policy = commissioned) {
  const env = {
    pr: makePR(),
    open: true,
    feed: null,
    runs: [],
    calls: [],
    loads: 0,
    files: [
      { filename: "submissions/new-proof/manifest.json", status: "added" },
    ],
    failDispatch: false,
    currentHead: null,
  };
  const api = async (route, options = {}) => {
    env.calls.push({ route, ...options });
    if (route.includes("/contents/submissions.json?"))
      return (
        env.feed && {
          sha: "stored-sha",
          content: Buffer.from(JSON.stringify(env.feed)).toString("base64"),
        }
      );
    if (route.includes("/pulls?state=open"))
      return env.open ? [structuredClone(env.pr)] : [];
    if (route.includes("/pulls/7/files?")) return env.files;
    if (route.endsWith("/pulls/7"))
      return {
        ...env.pr,
        state: env.open ? "open" : "closed",
        head: { ...env.pr.head, sha: env.currentHead ?? env.pr.head.sha },
      };
    if (route.endsWith("/actions/workflows/verify-submission.yml"))
      return { id: 123 };
    if (route.includes("/actions/workflows/123/runs?"))
      return { workflow_runs: env.runs };
    if (route.endsWith("/dispatches")) {
      if (env.failDispatch) throw Error("Dispatch unavailable");
      return null;
    }
    if (route.endsWith("/git/blobs")) {
      env.feed = JSON.parse(options.body.content);
      return { sha: "blob" };
    }
    if (route.endsWith("/git/trees")) return { sha: "tree" };
    if (route.endsWith("/git/commits")) return { sha: "commit" };
    if (route.endsWith("/git/refs")) return {};
    if (
      route.endsWith("/contents/submissions.json") &&
      options.method === "PUT"
    ) {
      env.feed = JSON.parse(
        Buffer.from(options.body.content, "base64").toString(),
      );
      return {};
    }
    throw Error("Unexpected test API route: " + route);
  };
  env.sync = () =>
    synchronizeSubmissions({
      repo,
      defaultBranch: "main",
      policy,
      api,
      now: "2026-10-10T12:00:00Z",
      load: async () => {
        env.loads++;
        return structuredClone(candidate);
      },
    });
  env.dispatches = () =>
    env.calls.filter((c) => c.route.endsWith("/dispatches"));
  return env;
}
function run(overrides = {}) {
  return {
    id: 42,
    run_attempt: 1,
    workflow_id: 123,
    event: "workflow_dispatch",
    head_branch: "main",
    display_title: `Verify PR 7 at ${head}`,
    status: "completed",
    conclusion: "success",
    ...overrides,
  };
}

test("intake records fork metadata and dispatches only the exact head on the default branch", async () => {
  const f = fixture();
  const feed = await f.sync();
  assert.equal(feed.records[0].state, "queued");
  assert.equal(feed.records[0].title, candidate.title);
  assert.deepEqual(f.dispatches()[0].body, {
    ref: "main",
    inputs: { pr: "7", head_sha: head },
  });
  assert.deepEqual(
    f.calls.find((c) => c.route.endsWith("/git/commits")).body.parents,
    [],
  );
  assert.equal(
    f.calls.find((c) => c.route.endsWith("/git/refs")).body.ref,
    "refs/heads/submission-status",
  );
  assert.ok(f.calls.every((c) => !/registry|check-runs/.test(c.route)));
});

test("uncommissioned workers leave submissions pending without scheduling proof execution", async () => {
  const f = fixture({
    repository: null,
    worker_image: null,
    acceptance_receipt_sha256: null,
    verification_keys: {},
  });
  assert.equal((await f.sync()).records[0].state, "awaiting-worker");
  assert.equal(f.dispatches().length, 0);
});

test("repeat events are idempotent and do not reload sources or dispatch again", async () => {
  const f = fixture();
  await f.sync();
  const calls = f.calls.length;
  await f.sync();
  assert.equal(f.dispatches().length, 1);
  assert.equal(f.loads, 1);
  assert.ok(f.calls.slice(calls).every((c) => !c.method));
});

test("new heads retain the prior revision and cannot inherit a stale successful run", async () => {
  const f = fixture();
  await f.sync();
  f.pr.head.sha = "d".repeat(40);
  f.runs = [run()];
  const feed = await f.sync();
  assert.equal(feed.records[0].state, "superseded");
  assert.equal(feed.records[1].state, "queued");
  assert.equal(feed.records[1].run_id, null);
  assert.equal(f.dispatches()[1].body.inputs.head_sha, f.pr.head.sha);
});

test("only trusted exact-head workflow results update pending state; success is not admission", async () => {
  const f = fixture();
  await f.sync();
  f.runs = [
    run({ head_branch: "attacker" }),
    run({ workflow_id: 999 }),
    run({ display_title: "Verify PR 7 at current head" }),
  ];
  assert.equal((await f.sync()).records[0].state, "queued");
  f.runs = [run({ status: "in_progress", conclusion: null })];
  assert.equal((await f.sync()).records[0].state, "running");
  f.runs = [run()];
  const record = (await f.sync()).records[0];
  assert.equal(record.state, "checks-passed");
  assert.equal(record.run_url, `https://github.com/${repo}/actions/runs/42`);
  assert.ok(!("first_verified_at" in record));
  assert.ok(!("status" in record));
});

test("drafts are logged and dispatch when ready, while closed PR history is retained", async () => {
  const f = fixture();
  f.pr.draft = true;
  assert.equal((await f.sync()).records[0].state, "draft");
  assert.equal(f.dispatches().length, 0);
  f.pr.draft = false;
  assert.equal((await f.sync()).records[0].state, "queued");
  f.open = false;
  assert.equal((await f.sync()).records[0].state, "closed");
  assert.equal(f.dispatches().length, 1);
});

test("an empty repository gets an empty feed without executing ordinary website PRs", async () => {
  const f = fixture();
  f.files = [{ filename: "src/App.tsx", status: "modified" }];
  assert.deepEqual((await f.sync()).records, []);
  assert.equal(f.loads, 0);
  assert.equal(f.dispatches().length, 0);
  assert.ok(f.feed);
});

test("mixed workflow edits and submissions are refused before fetching candidate data", async () => {
  const f = fixture();
  f.files.push({
    filename: ".github/workflows/verify-submission.yml",
    status: "modified",
  });
  assert.deepEqual((await f.sync()).records, []);
  assert.equal(f.loads, 0);
  assert.equal(f.dispatches().length, 0);
});

test("a head changing during intake is not recorded or dispatched", async () => {
  const f = fixture();
  f.currentHead = "e".repeat(40);
  assert.deepEqual((await f.sync()).records, []);
  assert.equal(f.dispatches().length, 0);
});

test("dispatch failure remains visible and can be retried by reconciliation", async () => {
  const f = fixture();
  f.failDispatch = true;
  assert.equal((await f.sync()).records[0].state, "dispatch-failed");
  f.failDispatch = false;
  assert.equal((await f.sync()).records[0].state, "queued");
});

test("privileged intake uses pinned trusted orchestration without downloading PR artifacts", () => {
  const workflow = readFileSync(
    ".github/workflows/submission-intake.yml",
    "utf8",
  );
  assert.match(workflow, /pull_request_target/);
  assert.match(workflow, /ref: \$\{\{ github.workflow_sha \}\}/);
  assert.match(workflow, /persist-credentials: false/);
  assert.doesNotMatch(
    workflow,
    /pull_request.head|download-artifact|secrets\./,
  );
  for (const line of workflow.split("\n").filter((l) => l.includes("uses:")))
    assert.match(line, /@[a-f0-9]{40}(?:\s|$)/);
});
