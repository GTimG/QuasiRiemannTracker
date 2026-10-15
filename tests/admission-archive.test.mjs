import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
  admissionPath,
  admissionRecord,
  archiveAdmission,
  validateAdmissionRecord,
} from "../verifier/admission-archive.mjs";
import { workerCertificate } from "../verifier/certificate.mjs";

const hex = (character) => character.repeat(40);
const repo = "owner/repository";
function fixture() {
  const expected = {
    repository: repo,
    number: 26,
    head_sha: hex("a"),
    result_id: "candidate-proof",
    theta_exact: "7/8",
  };
  const report = {
    status: "PASS",
    verified_at: "2026-10-13T00:00:00Z",
    reviewed_pr_head: expected.head_sha,
    source_repository: repo,
    result_id: expected.result_id,
    theta_exact: expected.theta_exact,
    judge_exit_code: 0,
    targets: ["QRH.canonical_bound"],
    kernels: ["Lean default", "nanoda", "con-ron"],
    allowed_axioms: ["propext", "Classical.choice", "Quot.sound"],
    sandbox_preflight: "PASS",
    candidate_mount_preflight: "PASS",
    challenge_exported_before_candidate_execution: true,
    receipt_outside_candidate: true,
  };
  const reportBytes = Buffer.from(JSON.stringify(report));
  return {
    expected,
    metadata: {
      title: "A candidate bound",
      authors: [{ name: "Contributor" }],
      description: "An independently verified proof.",
    },
    context: {
      repository: repo,
      defaultBranch: "main",
      run_id: "1234",
      run_attempt: "1",
      workflow_sha: hex("b"),
      check_id: 1235,
    },
    pr: {
      number: 26,
      state: "open",
      head: { sha: expected.head_sha },
      base: { ref: "main", repo: { full_name: repo } },
      title: "A candidate bound",
      body: 'QRH-Result: candidate-proof\nQRH-Bound: 7/8\nQRH-Decimal: 0.875\n\n```qrh-metadata\n{"title":"A candidate bound","authors":[{"name":"Contributor"}],"description":"An independently verified proof."}\n```',
      created_at: "2026-10-12T00:00:00Z",
      user: { login: "contributor" },
    },
    record: workerCertificate(
      expected,
      report,
      `https://github.com/${repo}/actions/runs/1234/attempts/1`,
      reportBytes,
    ),
    reportBytes,
  };
}

function response(data, status = 200) {
  return { ok: status >= 200 && status < 300, status, json: async () => data };
}

function api(steps) {
  const requests = [];
  const fetcher = async (url, options) => {
    const route = url.replace(`https://api.github.com/repos/${repo}/`, "");
    const body = options.body ? JSON.parse(options.body) : undefined;
    requests.push({ route, method: options.method, body });
    const step = steps.shift();
    assert.ok(step, `Unexpected request: ${options.method} ${route}`);
    assert.equal(options.method, step.method ?? "GET");
    assert.equal(route, step.route);
    step.inspect?.(body);
    if (step.error) throw step.error;
    return response(step.data, step.status);
  };
  return { fetcher, requests, token: "secret-token" };
}

const sourceSteps = () => [
  {
    route: `git/trees/${hex("a")}`,
    data: {
      tree: [
        { path: "submissions", mode: "040000", type: "tree", sha: hex("c") },
      ],
    },
  },
  {
    route: `git/trees/${hex("c")}`,
    data: {
      tree: [
        {
          path: "candidate-proof",
          mode: "040000",
          type: "tree",
          sha: hex("d"),
        },
      ],
    },
  },
  {
    route: `git/trees/${hex("d")}`,
    data: {
      tree: [{ path: "src", mode: "040000", type: "tree", sha: hex("e") }],
    },
  },
];
const path = `records/26/${hex("a")}/candidate-proof/1234-1.json`;
const savedResponse = (record) => ({
  type: "file",
  encoding: "base64",
  size: Buffer.byteLength(JSON.stringify(record)),
  content: Buffer.from(JSON.stringify(record)).toString("base64"),
});

test("archives an immutable verified envelope on an orphan data branch", async () => {
  const data = fixture();
  const steps = [
    ...sourceSteps(),
    { route: "git/ref/heads/admission-records", status: 404 },
    {
      route: "git/blobs",
      method: "POST",
      data: { sha: hex("1") },
      inspect: (body) => {
        const envelope = validateAdmissionRecord(JSON.parse(body.content));
        assert.equal(envelope.source_tree, hex("e"));
        assert.equal(envelope.report_json, data.reportBytes.toString());
        assert.deepEqual(envelope.certificate, data.record);
        assert.deepEqual(envelope.pr.author, {
          login: "contributor",
          url: "https://github.com/contributor",
        });
      },
    },
    {
      route: "git/trees",
      method: "POST",
      data: { sha: hex("2") },
      inspect: (body) =>
        assert.deepEqual(body, {
          tree: [{ path, mode: "100644", type: "blob", sha: hex("1") }],
        }),
    },
    {
      route: "git/commits",
      method: "POST",
      data: { sha: hex("3") },
      inspect: (body) => assert.deepEqual(body.parents, []),
    },
    {
      route: "git/refs",
      method: "POST",
      status: 201,
      data: {},
      inspect: (body) =>
        assert.deepEqual(body, {
          ref: "refs/heads/admission-records",
          sha: hex("3"),
        }),
    },
  ];
  const client = api(steps);
  assert.equal((await archiveAdmission(data, client)).commit, hex("3"));
  assert.equal(steps.length, 0);
  assert.ok(
    client.requests.every((r) => !r.route.includes("actions/artifacts")),
  );
});

test("a rerun keeps the first durable certificate without overwriting it", async () => {
  const data = fixture();
  const saved = admissionRecord({ ...data, sourceTree: hex("e") });
  const steps = [
    ...sourceSteps(),
    {
      route: "git/ref/heads/admission-records",
      data: { object: { sha: hex("3") } },
    },
    { route: `contents/${path}?ref=${hex("3")}`, data: savedResponse(saved) },
  ];
  const client = api(steps);
  const result = await archiveAdmission(data, client);
  assert.deepEqual(result.record, saved);
  assert.equal(steps.length, 0);
  assert.ok(client.requests.every((r) => r.method === "GET"));
});

test("large archived reports are reread through the immutable Git Blob API", async () => {
  const data = fixture();
  const saved = admissionRecord({ ...data, sourceTree: hex("e") });
  const steps = [
    ...sourceSteps(),
    {
      route: "git/ref/heads/admission-records",
      data: { object: { sha: hex("3") } },
    },
    {
      route: `contents/${path}?ref=${hex("3")}`,
      data: {
        type: "file",
        encoding: "none",
        content: "",
        sha: hex("4"),
        size: 1048577,
      },
    },
    { route: `git/blobs/${hex("4")}`, data: savedResponse(saved) },
  ];
  assert.deepEqual((await archiveAdmission(data, api(steps))).record, saved);
  assert.equal(steps.length, 0);
});

test("GitHub App authors retain a valid attribution link", () => {
  const data = fixture();
  data.pr.user.login = "github-actions[bot]";
  assert.deepEqual(
    admissionRecord({ ...data, sourceTree: hex("e") }).pr.author,
    {
      login: "github-actions[bot]",
      url: "https://github.com/apps/github-actions",
    },
  );
});

test("concurrent appends retry using the new parent and preserve its tree", async () => {
  const steps = [...sourceSteps()];
  for (const [i, parent, baseTree, nextCommit] of [
    [0, hex("3"), hex("4"), hex("5")],
    [1, hex("6"), hex("7"), hex("8")],
  ]) {
    steps.push(
      {
        route: "git/ref/heads/admission-records",
        data: { object: { sha: parent } },
      },
      { route: `contents/${path}?ref=${parent}`, status: 404 },
      { route: `git/commits/${parent}`, data: { tree: { sha: baseTree } } },
      ...(!i
        ? [{ route: "git/blobs", method: "POST", data: { sha: hex("1") } }]
        : []),
      {
        route: "git/trees",
        method: "POST",
        data: { sha: hex("2") },
        inspect: (body) => assert.equal(body.base_tree, baseTree),
      },
      {
        route: "git/commits",
        method: "POST",
        data: { sha: nextCommit },
        inspect: (body) => assert.deepEqual(body.parents, [parent]),
      },
      {
        route: "git/refs/heads/admission-records",
        method: "PATCH",
        status: !i ? 422 : 200,
        data: {},
        inspect: (body) =>
          assert.deepEqual(body, { sha: nextCommit, force: false }),
      },
    );
  }
  const client = api(steps);
  assert.equal((await archiveAdmission(fixture(), client)).commit, hex("8"));
  assert.equal(steps.length, 0);
  assert.equal(
    client.requests.filter((r) => r.route === "git/blobs").length,
    1,
  );
});

test("simultaneous branch creation safely rereads the winning record", async () => {
  const data = fixture();
  const saved = admissionRecord({ ...data, sourceTree: hex("e") });
  const steps = [
    ...sourceSteps(),
    { route: "git/ref/heads/admission-records", status: 404 },
    { route: "git/blobs", method: "POST", data: { sha: hex("1") } },
    { route: "git/trees", method: "POST", data: { sha: hex("2") } },
    { route: "git/commits", method: "POST", data: { sha: hex("3") } },
    { route: "git/refs", method: "POST", status: 422 },
    {
      route: "git/ref/heads/admission-records",
      data: { object: { sha: hex("4") } },
    },
    { route: `contents/${path}?ref=${hex("4")}`, data: savedResponse(saved) },
  ];
  assert.equal((await archiveAdmission(data, api(steps))).commit, hex("4"));
  assert.equal(steps.length, 0);
});

for (const key of ["head_sha", "result_id", "theta_exact", "source_tree"])
  test(`rejects an archive with mismatched ${key}`, async () => {
    const data = fixture();
    const saved = admissionRecord({ ...data, sourceTree: hex("e") });
    saved[key] =
      key.endsWith("sha") || key.endsWith("tree") ? hex("9") : "different";
    const steps = [
      ...sourceSteps(),
      {
        route: "git/ref/heads/admission-records",
        data: { object: { sha: hex("3") } },
      },
      { route: `contents/${path}?ref=${hex("3")}`, data: savedResponse(saved) },
    ];
    await assert.rejects(
      archiveAdmission(data, api(steps)),
      /Invalid|differs|conflicts/,
    );
  });

test("report bytes and complete kernel acceptance remain bound to the certificate", () => {
  const value = admissionRecord({ ...fixture(), sourceTree: hex("e") });
  value.report_json += " ";
  assert.throws(() => validateAdmissionRecord(value), /report differs/);
});

test("publication metadata cannot differ from the exact admitted source metadata", () => {
  const value = admissionRecord({ ...fixture(), sourceTree: hex("e") });
  value.metadata.title = "An unreviewed title";
  assert.throws(() => validateAdmissionRecord(value), /metadata differs/);
});

test("separate runs preserve their immutable metadata snapshots", () => {
  const data = fixture();
  const paths = new Set();
  for (const [runId, title] of [
    ["1234", "First title"],
    ["1235", "Second title"],
    ["1236", "First title"],
  ]) {
    const revision = structuredClone(data);
    revision.reportBytes = data.reportBytes;
    revision.context.run_id = runId;
    revision.record.report_url = `https://github.com/${repo}/actions/runs/${runId}/attempts/1`;
    revision.metadata.title = title;
    revision.pr.body = revision.pr.body.replace(
      '"title":"A candidate bound"',
      `"title":"${title}"`,
    );
    const envelope = admissionRecord({ ...revision, sourceTree: hex("e") });
    paths.add(admissionPath(envelope));
    assert.equal(envelope.metadata.title, title);
    assert.ok(Number.isFinite(Date.parse(envelope.admission.archived_at)));
  }
  assert.equal(paths.size, 3);
});

test("a workflow retry cannot silently replace metadata for the same attempt", async () => {
  const data = fixture();
  const saved = admissionRecord({ ...data, sourceTree: hex("e") });
  saved.metadata.title = "Different title";
  saved.pr.body = saved.pr.body.replace(
    '"title":"A candidate bound"',
    '"title":"Different title"',
  );
  const steps = [
    ...sourceSteps(),
    {
      route: "git/ref/heads/admission-records",
      data: { object: { sha: hex("3") } },
    },
    { route: `contents/${path}?ref=${hex("3")}`, data: savedResponse(saved) },
  ];
  await assert.rejects(
    archiveAdmission(data, api(steps)),
    /identity conflicts|metadata differs/,
  );
});

test("source traversal rejects a symlink or truncated response before writing", async () => {
  for (const invalid of [
    {
      tree: [
        { path: "submissions", mode: "120000", type: "blob", sha: hex("c") },
      ],
    },
    { ...sourceSteps()[0].data, truncated: true },
  ]) {
    const client = api([{ route: `git/trees/${hex("a")}`, data: invalid }]);
    await assert.rejects(archiveAdmission(fixture(), client), /source tree/);
    assert.equal(client.requests.length, 1);
  }
});

test("transport failures never expose credentials through errors", async () => {
  const client = api([
    {
      route: `git/trees/${hex("a")}`,
      error: Error("Authorization: Bearer secret-token"),
    },
  ]);
  await assert.rejects(archiveAdmission(fixture(), client), (error) => {
    assert.equal(error.message, "GitHub admission archive request failed");
    return !error.message.includes("secret-token");
  });
});

test("only the trusted publisher receives archive write permission", () => {
  const workflow = readFileSync(
    new URL("../.github/workflows/pr-admission.yml", import.meta.url),
    "utf8",
  );
  const verify = workflow.split("  verify:\n")[1].split("  admission:\n")[0];
  const publish = workflow.split("  admission:\n")[1];
  assert.match(verify, /contents: read/);
  assert.doesNotMatch(verify, /contents: write/);
  assert.match(publish, /contents: write/);
  assert.match(publish, /ref: \$\{\{ github\.workflow_sha \}\}/);
  assert.match(publish, /persist-credentials: false/);
});
