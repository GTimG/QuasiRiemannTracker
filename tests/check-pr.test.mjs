import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import {
  mkdirSync,
  mkdtempSync,
  rmSync,
  writeFileSync,
  readFileSync,
  existsSync,
} from "node:fs";
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

test("missing publication metadata fails before queuing a proof worker", (t) => {
  const data = fixture([
    {
      filename: "submissions/example-bound/src/Candidate/Main.lean",
      status: "added",
    },
  ]);
  data.pr.body =
    "QRH-Result: example-bound\nQRH-Bound: 7/8\nQRH-Decimal: 0.875";
  data.omitMetadata = true;
  const result = run(t, data, { QRH_PHASE: "prepare" });
  assertFailure(result, "Expected a regular submission metadata.json");
  assert.equal(result.context, null);
});

// This child replaces fetch before importing the executable module. The mock
// handles every API read and write and rejects unknown requests.
const harness = `
const fixture = JSON.parse(process.env.QRH_TEST_FIXTURE);
const number = fixture.pr.number;
const requests = [];
const cp = (await import("node:child_process")).default;
const originalExec = cp.execFileSync;
cp.execFileSync = (command, args, options) => {
  if (command !== "git") return originalExec(command, args, options);
  const offset = args.indexOf("core.hooksPath=/dev/null") + 1;
  const op = args.slice(offset);
  const snapshots = fixture.snapshots || {base:{"catalogue/results.json":{schema_version:1,records:[]}},head:{"catalogue/results.json":{schema_version:1,records:[]}}};
  const side = sha => sha === fixture.pr.head.sha ? "head" : "base";
  if (op[0] === "ls-tree") {
    const ref = op[op.indexOf("--")-1], path = op.at(-1), data = snapshots[side(ref)];
    if (op.includes("-r")) return Object.keys(data).filter(p=>p.startsWith(path)).join(String.fromCharCode(10));
    return Object.hasOwn(data, path) ? "100644 blob " + "d".repeat(40) + String.fromCharCode(9) + path + String.fromCharCode(10) : "";
  }
  if (op[0] === "show") {
    const split = op[1].indexOf(":"), ref = op[1].slice(0,split), path = op[1].slice(split+1);
    return JSON.stringify(snapshots[side(ref)][path]);
  }
  if (["init","remote","config","fetch"].includes(op[0])) return "";
  throw Error("Unexpected git call: " + JSON.stringify(op));
};
(await import("node:module")).syncBuiltinESMExports();
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
  if (request.method === "GET" && route.includes("/git/trees/")) {
    const key=route.split("/").at(-1), id=/QRH-Result: ([^\\n]+)/.exec(fixture.pr.body)[1];
    const item=(path,sha,type="tree",mode="040000")=>({path,sha:sha.repeat(40),type,mode});
    value={tree:key===fixture.pr.head.sha?[item("submissions","d")]:key==="d".repeat(40)?[item(id,"e")]:key==="e".repeat(40)?[item("src","f"),...(fixture.omitMetadata?[]:[item("metadata.json","1","blob","100644")])]:key==="f".repeat(40)?[item("Candidate","2")]:[item("Main.lean","3","blob","100644")]};
  } else if (request.method === "GET" && route.includes("/git/blobs/")) {
    value={encoding:"base64",size:100,content:Buffer.from(JSON.stringify({title:"Fixture result",authors:[{name:"Fixture author"}],description:"Synthetic proof description."})).toString("base64")};
  } else if (request.method === "GET" && route === "/repos/${repository}/pulls/" + number) {
    value = prReads++ === 0 ? fixture.pr : (fixture.current ?? fixture.pr);
  } else if (request.method === "GET" && route === "/repos/${repository}/pulls/" + number + "/files") {
    if (parsed.searchParams.get("per_page") !== "100") throw Error("Unexpected page size");
    const page = Number(parsed.searchParams.get("page"));
    value = fixture.files.slice((page - 1) * 100, page * 100);
  } else if (request.method === "GET" && route === "/repos/${repository}/issues/" + number + "/labels") {
    const page = Number(parsed.searchParams.get("page"));
    value = (fixture.labels ?? []).slice((page - 1) * 100, page * 100);
  } else if (request.method === "GET" && route.startsWith("/repos/${repository}/labels/")) {
    value = { name: decodeURIComponent(route.split("/").at(-1)) };
  } else if (request.method === "POST" && route === "/repos/${repository}/issues/" + number + "/labels") {
    if (fixture.labelWriteStatus) return { ok: false, status: fixture.labelWriteStatus };
    value = request.body.labels.map(name => ({ name }));
  } else if (request.method === "DELETE" && route.startsWith("/repos/${repository}/issues/" + number + "/labels/")) {
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
  data = structuredClone(data);
  if (!data.omitMetadata) {
    for (const pr of [data.pr, data.current].filter(Boolean)) {
      if (
        pr.body?.includes("QRH-Result:") &&
        !pr.body.includes("```qrh-metadata")
      )
        pr.body +=
          '\n\n```qrh-metadata\n{"title":"Fixture result","authors":[{"name":"Fixture author"}],"description":"Synthetic proof description."}\n```';
    }
  }
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
        GITHUB_OUTPUT: join(cwd, "outputs"),
        GITHUB_RUN_ATTEMPT: "1",
        GITHUB_WORKFLOW_SHA: "c".repeat(40),
        QRH_PR: String(data.pr.number),
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
    context: existsSync(join(cwd, "verification-context/context.json"))
      ? JSON.parse(
          readFileSync(join(cwd, "verification-context/context.json"), "utf8"),
        )
      : null,
    outputs: existsSync(join(cwd, "outputs"))
      ? readFileSync(join(cwd, "outputs"), "utf8")
      : "",
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

function assertFailure(result, message) {
  assert.equal(result.status, 1);
  assert.equal(result.importError, undefined);
  assert.equal(result.checkWrites.length, 2);
  const completed = result.checkWrites.at(-1).body;
  assert.equal(completed.status, "completed");
  assert.equal(completed.conclusion, "failure");
  assert.equal(completed.output.title, "PR admission failed");
  assert.equal(completed.output.summary, `Admission failed: ${message}`);
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

test("unmarked cleanup across multiple file pages receives maintenance and succeeds", (t) => {
  const files = Array.from({ length: 100 }, (_, i) => ({
    filename: `docs/page-${i}.md`,
    status: "modified",
  }));
  files.push({ filename: "proofs/candidate/Main.lean", status: "removed" });
  const result = run(t, fixture(files), { QRH_PHASE: "prepare" });
  assert.equal(result.status, 0);
  assert.equal(result.checkWrites.at(-1).body.conclusion, "success");
  assert.equal(result.context, null);
  assert.equal(result.outputs, "");
  assert.deepEqual(
    result.requests
      .filter((r) => new URL(r.url).pathname.endsWith("/files"))
      .map((r) => new URL(r.url).searchParams.get("page")),
    ["1", "2"],
  );
  assert.deepEqual(
    result.labelWrites.map((r) => r.body?.labels),
    [["maintenance"]],
  );
});

test("an open maintenance draft publishes successful admission and receives its label", (t) => {
  const data = fixture();
  data.pr.draft = true;
  const result = run(t, data);
  assert.equal(result.status, 0);
  assert.equal(result.importError, undefined);
  assert.equal(result.checkWrites.at(-1).body.status, "completed");
  assert.equal(result.checkWrites.at(-1).body.conclusion, "success");
  assert.deepEqual(
    result.labelWrites.map((request) => request.body?.labels),
    [["maintenance"]],
  );
});

test("publishes admission failure when a required label write fails", (t) => {
  const data = fixture();
  data.labelWriteStatus = 403;
  const result = run(t, data);
  assertFailure(
    result,
    `GitHub API 403 for repos/${repository}/issues/15/labels`,
  );
  assert.deepEqual(
    result.labelWrites.map((request) => request.body?.labels),
    [["maintenance"]],
  );
});

for (const draft of [false, true]) {
  test(`PR #15 publishes the live verification failure as ${draft ? "a draft" : "ready for review"}`, (t) => {
    const data = fixture([
      {
        filename:
          "submissions/gao-local-moment-20261011/src/Candidate/Main.lean",
        status: "added",
      },
    ]);
    data.pr.draft = draft;
    data.pr.body =
      "QRH-Result: gao-local-moment-20261011\nQRH-Bound: 4374433/5000000\nQRH-Decimal: 0.87488660";
    const result = run(t, data);
    assertFailure(result, "Proof verification has not run for this PR head");
    assert.deepEqual(
      result.labelWrites.map((request) => request.body?.labels),
      [["new-bound"]],
    );
  });
}

for (const [description, maintenanceFiles, message, labels] of [
  [
    "mixed changes",
    [{ filename: "tests/browser/dashboard.spec.ts", status: "modified" }],
    "Submit QRH results and maintenance changes in separate PRs",
    ["new-bound", "maintenance"],
  ],
  [
    "a proof-only submission",
    [],
    "Proof verification has not run for this PR head",
    ["new-bound"],
  ],
]) {
  test(`PR #8 publishes the admission reason for ${description}`, (t) => {
    const data = fixture([
      {
        filename:
          "submissions/single-prime-29-33-20261010/src/Candidate/Main.lean",
        status: "added",
      },
      ...maintenanceFiles,
    ]);
    data.pr.number = 8;
    data.pr.body =
      "QRH-Result: single-prime-29-33-20261010\nQRH-Bound: 29/33\nQRH-Decimal: 0.87878787";
    const result = run(t, data);
    assertFailure(result, message);
    assert.deepEqual(
      result.labelWrites.map((request) => request.body?.labels),
      [labels],
    );
  });
}

test("a theta 1 submission publishes the live verification failure", (t) => {
  const data = fixture([
    {
      filename: "submissions/theta-one/src/Candidate/Main.lean",
      status: "added",
    },
  ]);
  data.pr.number = 5;
  data.pr.body = "QRH-Result: theta-one\nQRH-Bound: 1/1\nQRH-Decimal: 1.0";
  const result = run(t, data);
  assertFailure(result, "Proof verification has not run for this PR head");
  assert.deepEqual(
    result.labelWrites.map((request) => request.body?.labels),
    [["new-bound"]],
  );
});

test("an incomplete file list fails before assigning classification labels", (t) => {
  const data = fixture();
  data.pr.changed_files = 2;
  const result = run(t, data);
  assertFailure(
    result,
    "Incomplete or duplicate PR file list; refusing a truncated diff",
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
    assertFailure(
      result,
      "PR head, base or declaration changed during validation; rerun admission",
    );
    assert.equal(result.checkWrites[0].body.head_sha, head);
  }
});

test("requires the default branch before reading or publishing checks", (t) => {
  const result = run(t, fixture(), {
    GITHUB_REF: "refs/heads/untrusted-candidate",
  });
  assert.equal(result.status, 1);
  assert.equal(
    result.importError,
    "Trusted default-branch PR admission orchestration required",
  );
  assert.deepEqual(result.requests, []);
  assert.deepEqual(result.checkWrites, []);
  assert.deepEqual(result.labelWrites, []);
});

for (const draft of [false, true]) {
  test(`queues live proof verification for draft=${draft}`, (t) => {
    const data = fixture([
      {
        filename: "submissions/candidate/src/Candidate/Main.lean",
        status: "added",
      },
    ]);
    data.pr.draft = draft;
    data.pr.body = "QRH-Result: candidate\nQRH-Bound: 1/1\nQRH-Decimal: 1.0";
    const result = run(t, data, { QRH_PHASE: "prepare" });
    assert.equal(result.status, 0);
    assert.equal(result.checkWrites.length, 1);
    assert.equal(result.checkWrites[0].body.status, "in_progress");
    assert.equal(result.outputs, 'verify=true\nmatrix=["candidate"]\n');
    assert.deepEqual(result.context.expected, {
      repository,
      number: 15,
      head_sha: head,
      result_id: "candidate",
      theta_exact: "1/1",
    });
    assert.equal(result.context.check_id, 123);
    assert.equal(result.context.run_id, "456");
  });
}

for (const draft of [false, true]) {
  test(`cleanup defaults to maintenance without queuing a proof for draft=${draft}`, (t) => {
    const data = fixture([
      { filename: "proofs/old/Main.lean", status: "removed" },
      { filename: "catalogue/results.json", status: "removed" },
      { filename: "src/App.tsx", status: "modified" },
    ]);
    data.pr.draft = draft;
    data.pr.body = "Clean up the codebase.";
    data.labels = [{ name: "new-bound" }];
    const result = run(t, data, { QRH_PHASE: "prepare" });
    assert.equal(result.status, 0);
    assert.equal(result.checkWrites.at(-1).body.conclusion, "success");
    assert.equal(result.context, null);
    assert.equal(result.outputs, "");
    assert.deepEqual(
      result.labelWrites.map((r) => [r.method, r.body?.labels]),
      [
        ["POST", ["maintenance"]],
        ["DELETE", undefined],
      ],
    );
  });
}

for (const draft of [false, true]) {
  test(`maintenance queues source checks while retaining maintenance label for draft=${draft}`, (t) => {
    const data = fixture([
      {
        filename: "submissions/candidate/src/Candidate/Main.lean",
        status: "modified",
      },
      { filename: "src/App.tsx", status: "modified" },
    ]);
    data.pr.draft = draft;
    data.pr.body = "";
    const catalogue = {
      schema_version: 1,
      records: [
        {
          id: "candidate",
          theta: { numerator: "1", denominator: "1" },
          status: "verification-pending",
          timeline_at: "2026-10-01T00:00:00Z",
          date_label: "Submitted",
          verification_note: "Pending",
          authors: [{ name: "Author" }],
          references: [{ url: "https://example.com/proof" }],
          title: "Candidate",
          method: "Proof",
          builds_on: [],
        },
      ],
    };
    data.snapshots = {
      base: Object.fromEntries(
        catalogue.records.flatMap((r) => [
          [`submissions/${r.id}/metadata.json`, r],
          [`submissions/${r.id}/src/Candidate/Main.lean`, "theorem"],
        ]),
      ),
      head: {
        ...Object.fromEntries(
          catalogue.records.flatMap((r) => [
            [`submissions/${r.id}/metadata.json`, r],
            [`submissions/${r.id}/src/Candidate/Main.lean`, "theorem"],
          ]),
        ),
        "submissions/candidate/src/Candidate/Main.lean": "theorem",
      },
    };
    const result = run(t, data, { QRH_PHASE: "prepare" });
    assert.equal(result.status, 0, JSON.stringify(result));
    assert.equal(result.checkWrites.length, 1);
    assert.deepEqual(
      result.labelWrites.map((r) => r.body?.labels),
      [["maintenance"]],
    );
    assert.equal(result.context.expectations.length, 1);
    assert.equal(result.context.expected.theta_exact, "1/1");
    assert.equal(result.context.expected.head_sha, head);
    assert.match(result.outputs, /matrix=\["candidate"\]/);
  });
}
