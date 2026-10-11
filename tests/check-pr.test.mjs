import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const repository = "GTimG/QuasiRiemannTracker";
const head = "a".repeat(40);
const entrypoint = new URL("../verifier/check-pr.mjs", import.meta.url).href;

function fixture(files = [{ filename: "README.md", status: "modified" }]) {
  return {
    pr: {
      number: 15,
      state: "open",
      draft: false,
      title: "Maintenance",
      body: "Updates the tracker documentation.",
      head: { sha: head, repo: { full_name: "Contributor/Tracker" } },
      base: {
        sha: "b".repeat(40),
        ref: "main",
        repo: { full_name: repository },
      },
      changed_files: files.length,
    },
    files,
  };
}

// This child replaces fetch before importing the executable module. The mock
// handles every API read and write and rejects unknown requests.
const harness = `
const fixture = JSON.parse(process.env.QRH_TEST_FIXTURE);
const requests = [];
let prReads = 0;
globalThis.fetch = async (url, options = {}) => {
  const request = {
    url: String(url),
    method: options.method ?? "GET",
    body: options.body ? JSON.parse(options.body) : undefined,
  };
  requests.push(request);
  const parsed = new URL(request.url);
  const route = parsed.pathname;
  if (parsed.origin !== "https://api.github.com") throw Error("Unexpected API origin");
  let value;
  if (request.method === "GET" && route === "/repos/${repository}/pulls/15") {
    value = prReads++ === 0 ? fixture.pr : (fixture.current ?? fixture.pr);
  } else if (request.method === "GET" && route === "/repos/${repository}/pulls/15/files") {
    if (parsed.searchParams.get("per_page") !== "100") throw Error("Unexpected page size");
    const page = Number(parsed.searchParams.get("page"));
    value = fixture.files.slice((page - 1) * 100, page * 100);
  } else if (request.method === "GET" && route === "/repos/${repository}/issues/15/labels") {
    const page = Number(parsed.searchParams.get("page"));
    value = (fixture.labels ?? []).slice((page - 1) * 100, page * 100);
  } else if (request.method === "GET" && route.startsWith("/repos/${repository}/labels/")) {
    value = { name: decodeURIComponent(route.split("/").at(-1)) };
  } else if (request.method === "POST" && route === "/repos/${repository}/issues/15/labels") {
    if (fixture.labelWriteStatus) return { ok: false, status: fixture.labelWriteStatus };
    value = request.body.labels.map(name => ({ name }));
  } else if (request.method === "DELETE" && route.startsWith("/repos/${repository}/issues/15/labels/")) {
    value = {};
  } else if (request.method === "POST" && route === "/repos/${repository}/check-runs") {
    value = { id: 123 };
  } else if (request.method === "PATCH" && route === "/repos/${repository}/check-runs/123") {
    value = { id: 123 };
  } else throw Error("Unexpected API request: " + request.method + " " + request.url);
  return { ok: true, status: 200, json: async () => structuredClone(value) };
};
let importError;
try { await import(${JSON.stringify(entrypoint)}); }
catch (error) { importError = error.message; process.exitCode = 1; }
console.log("MOCK_RESULT=" + JSON.stringify({ requests, importError }));
`;

function run(t, data, overrides = {}) {
  const cwd = mkdtempSync(join(tmpdir(), "qrh-check-pr-"));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  mkdirSync(join(cwd, "verifier"));
  writeFileSync(
    join(cwd, "verifier/pr-admissions.json"),
    JSON.stringify({ schema_version: 1, admissions: [] }),
  );
  const child = spawnSync(
    process.execPath,
    ["--input-type=module", "--eval", harness],
    {
      cwd,
      encoding: "utf8",
      timeout: 10_000,
      env: {
        GITHUB_REPOSITORY: repository,
        GITHUB_TOKEN: "synthetic-test-token",
        GITHUB_REF: "refs/heads/main",
        GITHUB_EVENT_NAME: "pull_request_target",
        GITHUB_RUN_ID: "456",
        QRH_PR: "15",
        QRH_DEFAULT_BRANCH: "main",
        QRH_TEST_FIXTURE: JSON.stringify(data),
        ...overrides,
      },
    },
  );
  assert.ifError(child.error);
  assert.equal(child.signal, null, child.stderr);
  const line = child.stdout
    .split("\n")
    .find((value) => value.startsWith("MOCK_RESULT="));
  assert.ok(line, `No mock results: ${child.stdout}\n${child.stderr}`);
  const result = JSON.parse(line.slice("MOCK_RESULT=".length));
  return {
    ...result,
    status: child.status,
    checkWrites: result.requests.filter(
      (request) =>
        request.method !== "GET" && request.url.includes("/check-runs"),
    ),
    labelWrites: result.requests.filter(
      (request) => request.method !== "GET" && request.url.includes("/labels"),
    ),
  };
}

test("maintenance publishes success and replaces a stale new-bound label", (t) => {
  const data = fixture();
  data.labels = [{ name: "new-bound" }, { name: "help wanted" }];
  const result = run(t, data);
  assert.equal(result.status, 0);
  assert.equal(result.importError, undefined);
  assert.equal(result.checkWrites.length, 2);
  const [created, completed] = result.checkWrites;
  assert.equal(created.method, "POST");
  assert.equal(created.body.name, "qrh/pr-admission");
  assert.equal(created.body.head_sha, head);
  assert.equal(created.body.status, "in_progress");
  assert.equal(completed.method, "PATCH");
  assert.equal(
    completed.url,
    `https://api.github.com/repos/${repository}/check-runs/123`,
  );
  assert.equal(completed.body.status, "completed");
  assert.equal(completed.body.conclusion, "success");
  assert.deepEqual(
    result.labelWrites.map(({ method, body, url }) => ({ method, body, url })),
    [
      {
        method: "POST",
        body: { labels: ["maintenance"] },
        url: `https://api.github.com/repos/${repository}/issues/15/labels`,
      },
      {
        method: "DELETE",
        body: undefined,
        url: `https://api.github.com/repos/${repository}/issues/15/labels/new-bound`,
      },
    ],
  );
});

test("a proof on the second changed-files page adds both labels and fails mixed admission", (t) => {
  const files = Array.from({ length: 100 }, (_, i) => ({
    filename: `docs/page-${i}.md`,
    status: "modified",
  }));
  files.push({ filename: "proofs/candidate/Main.lean", status: "added" });
  const result = run(t, fixture(files));
  assert.equal(result.status, 1);
  const pages = result.requests
    .filter((request) => new URL(request.url).pathname.endsWith("/files"))
    .map((request) => new URL(request.url).searchParams.get("page"));
  assert.deepEqual(pages, ["1", "2"]);
  assert.equal(result.checkWrites.at(-1).body.conclusion, "failure");
  assert.match(
    result.checkWrites.at(-1).body.output.summary,
    /[Ss]eparate|[Mm]ixed/,
  );
  assert.deepEqual(
    result.labelWrites.map((request) => request.body?.labels),
    [["new-bound", "maintenance"]],
  );
});

test("an open draft receives its maintenance label while admission fails", (t) => {
  const data = fixture();
  data.pr.draft = true;
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.deepEqual(
    result.labelWrites.map((request) => request.body?.labels),
    [["maintenance"]],
  );
  assert.equal(result.checkWrites.at(-1).body.conclusion, "failure");
  assert.match(result.checkWrites.at(-1).body.output.summary, /draft|ready/i);
});

test("publishes admission failure when a required label write fails", (t) => {
  const data = fixture();
  data.labelWriteStatus = 403;
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.deepEqual(
    result.labelWrites.map((request) => request.body?.labels),
    [["maintenance"]],
  );
  assert.equal(result.checkWrites.at(-1).body.conclusion, "failure");
  assert.match(result.checkWrites.at(-1).body.output.summary, /GitHub API 403/);
});

test("requires trusted evidence for a declared new bound", (t) => {
  const data = fixture([
    { filename: "proofs/candidate/Main.lean", status: "added" },
  ]);
  data.pr.body =
    "QRH-Result: candidate-20261011\nQRH-Bound: 4374433/5000000\nQRH-Decimal: 0.87488660";
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.equal(result.checkWrites.at(-1).body.conclusion, "failure");
  assert.match(
    result.checkWrites.at(-1).body.output.summary,
    /archive an independent maintainer replay/,
  );
  assert.deepEqual(
    result.labelWrites.map((request) => request.body?.labels),
    [["new-bound"]],
  );
});

test("an incomplete file list fails before assigning classification labels", (t) => {
  const data = fixture();
  data.pr.changed_files = 2;
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.equal(result.checkWrites.at(-1).body.conclusion, "failure");
  assert.match(
    result.checkWrites.at(-1).body.output.summary,
    /[Ii]ncomplete|truncated/,
  );
  assert.deepEqual(result.labelWrites, []);
  assert.ok(
    result.requests.every((request) => !request.url.includes("/labels")),
  );
});

test("publishes admission failure when the head or declaration changes during validation", (t) => {
  for (const change of ["head", "body"]) {
    const data = fixture();
    data.current = structuredClone(data.pr);
    if (change === "head") data.current.head.sha = "c".repeat(40);
    else data.current.body = "## New bound";
    const result = run(t, data);
    assert.equal(result.status, 1, change);
    assert.equal(result.checkWrites[0].body.head_sha, head);
    assert.equal(result.checkWrites.at(-1).body.conclusion, "failure", change);
    assert.match(
      result.checkWrites.at(-1).body.output.summary,
      /changed during validation/,
    );
  }
});

test("requires the default branch before reading or publishing checks", (t) => {
  const result = run(t, fixture(), {
    GITHUB_REF: "refs/heads/untrusted-candidate",
  });
  assert.equal(result.status, 1);
  assert.match(
    result.importError,
    /Trusted default-branch PR admission orchestration required/,
  );
  assert.deepEqual(result.requests, []);
  assert.deepEqual(result.checkWrites, []);
  assert.deepEqual(result.labelWrites, []);
});
