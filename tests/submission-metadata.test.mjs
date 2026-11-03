import test from "node:test";
import assert from "node:assert/strict";
import {
  parseSubmissionMetadata,
  readSubmissionMetadata,
  readSubmissionSources,
  validateSubmissionMetadata,
  validateAgentTraces,
  parseSubmissionMetadataJSON,
  maxMetadataBytes,
  maxAgentTracesBytes,
} from "../verifier/submission-metadata.mjs";

const metadata = () => ({
  title: "A candidate bound",
  authors: [{ name: "Example researcher", url: "https://example.org/author" }],
  description: "The argument improves a moment estimate.",
});
const block = (value) => "```qrh-metadata\n" + JSON.stringify(value) + "\n```";

test("v1 admission archives retain their original PR metadata", () => {
  const value = {
    ...metadata(),
    license: "Apache-2.0",
    builds_on: ["earlier-result"],
    references: [{ label: "Paper", url: "https://example.org/paper" }],
  };
  assert.deepEqual(
    parseSubmissionMetadata("QRH-Result: candidate-proof\n\n" + block(value)),
    value,
  );
});
test("invalid v1 archived metadata is rejected", () => {
  for (const body of [
    "",
    "A description without metadata",
    block(metadata()) + "\n" + block(metadata()),
    "```qrh-metadata\n{bad json}\n```",
  ])
    assert.throws(() => parseSubmissionMetadata(body), /metadata|JSON/);
});
test("publication metadata cannot provide verification claims or unsafe links", () => {
  for (const changes of [
    { status: "framework-verified" },
    { theta_exact: "1/2" },
    { title: "" },
    { authors: [] },
    { authors: [{ name: "Example", url: "javascript:alert(1)" }] },
    {
      references: [
        { label: "Paper", url: "https://user:password@example.org" },
      ],
    },
    { builds_on: ["../other-proof"] },
    { builds_on: ["earlier-result", "earlier-result"] },
  ])
    assert.throws(
      () => validateSubmissionMetadata({ ...metadata(), ...changes }),
      /Invalid publication metadata/,
    );
});

test("optional embedded traces preserve native exports without prescribing their format", () => {
  const value = {
    ...metadata(),
    agent_traces: [
      {
        schema_version: "ATIF-v1.7",
        steps: [{ message: "Checked the proof" }],
      },
      [{ role: "user", content: "Find a bound" }, { tool: { output: "done" } }],
    ],
  };
  assert.equal(validateSubmissionMetadata(value), value);
  assert.equal(validateAgentTraces(value), value.agent_traces);
  assert.deepEqual(validateAgentTraces(metadata()), []);
  assert.deepEqual(
    parseSubmissionMetadataJSON(Buffer.from(JSON.stringify(value))),
    value,
  );
  for (const agent_traces of [null, {}, "run.json", ["run.json"], [null], [1]])
    assert.throws(
      () => validateSubmissionMetadata({ ...metadata(), agent_traces }),
      /array of embedded JSON/,
    );
});

test("trace limits bound payload and nesting while retaining the publication metadata limit", () => {
  assert.throws(
    () =>
      validateAgentTraces({
        agent_traces: [{ output: "x".repeat(maxAgentTracesBytes) }],
      }),
    /at most 1 MiB/,
  );
  assert.throws(
    () => validateAgentTraces({ description: "x".repeat(65536) }),
    /excluding agent traces is too large/,
  );
  let trace = {};
  for (let i = 1; i < 64; i++) trace = { child: trace };
  assert.equal(validateAgentTraces({ agent_traces: [trace] })[0], trace);
  assert.throws(
    () => validateAgentTraces({ agent_traces: [{ child: trace }] }),
    /nesting.*64/,
  );
  for (const value of [undefined, Infinity, () => {}, new Date()])
    assert.throws(
      () => validateAgentTraces({ agent_traces: [{ value }] }),
      /only JSON data/,
    );
  const cyclic = {};
  cyclic.child = cyclic;
  assert.throws(
    () => validateAgentTraces({ agent_traces: [cyclic] }),
    /nesting/,
  );
});

test("metadata JSON parsing caps raw bytes and never exposes malformed trace fragments", () => {
  for (const bytes of [
    Buffer.from('{"agent_traces":[{"output":"private-credential" INVALID}]}'),
    Buffer.from([0xff, 0xfe]),
  ])
    assert.throws(
      () => parseSubmissionMetadataJSON(bytes),
      (error) =>
        error.message === "Submission metadata must contain valid UTF-8 JSON",
    );
  assert.throws(
    () => parseSubmissionMetadataJSON(" ".repeat(maxMetadataBytes) + "{}"),
    /metadata is too large/,
  );
});

function sourceApi({
  missingMain = false,
  mainMode = "100644",
  metadataMode = "100644",
  blob = null,
  directories = ["candidate-proof"],
} = {}) {
  const item = (path, sha, type = "tree", mode = "040000") => ({
    path,
    sha: sha.repeat(40),
    type,
    mode,
  });
  const routes = {
    ["git/trees/" + "a".repeat(40)]: { tree: [item("submissions", "b")] },
    ["git/trees/" + "b".repeat(40)]: {
      tree: directories.map((directory) => item(directory, "c")),
    },
    ["git/trees/" + "c".repeat(40)]: {
      tree: [
        item("src", "d"),
        item("metadata.json", "e", "blob", metadataMode),
      ],
    },
    ["git/trees/" + "d".repeat(40)]: { tree: [item("Candidate", "f")] },
    ["git/trees/" + "f".repeat(40)]: {
      tree: missingMain ? [] : [item("Main.lean", "1", "blob", mainMode)],
    },
    ["git/blobs/" + "e".repeat(40)]: blob ?? {
      encoding: "base64",
      size: 100,
      content: Buffer.from(JSON.stringify(metadata())).toString("base64"),
    },
  };
  return async (route) => {
    assert.ok(route.startsWith("repos/owner/repo/"));
    const key = route.slice("repos/owner/repo/".length);
    assert.ok(
      Object.hasOwn(routes, key),
      `Unexpected source request: ${route}`,
    );
    return routes[key];
  };
}
const expected = {
  repository: "owner/repo",
  head_sha: "a".repeat(40),
  result_id: "candidate-proof",
};
test("new submissions read metadata and require Lean source from the exact commit", async () => {
  assert.deepEqual(
    await readSubmissionMetadata(sourceApi(), expected),
    metadata(),
  );
  for (const blob of [{}, { encoding: "base64", size: 65537 }])
    await assert.rejects(
      readSubmissionMetadata(sourceApi({ blob }), expected),
      /regular.*metadata.json/,
    );
});
test("immutable metadata reads preserve embedded exports larger than the old 64 KiB cap", async () => {
  const value = {
    ...metadata(),
    agent_traces: [{ output: "x".repeat(70 * 1024) }],
  };
  const bytes = Buffer.from(JSON.stringify(value));
  const blob = {
    encoding: "base64",
    size: bytes.length,
    content: bytes.toString("base64"),
  };
  assert.deepEqual(
    await readSubmissionMetadata(sourceApi({ blob }), expected),
    value,
  );
  await assert.rejects(
    readSubmissionMetadata(
      sourceApi({ blob: { ...blob, size: maxMetadataBytes + 1 } }),
      expected,
    ),
    /regular.*metadata.json/,
  );
});
test("dated source paths preserve the result identity and original immutable tree", async () => {
  const historical = await readSubmissionSources(sourceApi(), expected);
  const dated = await readSubmissionSources(
    sourceApi({ directories: ["2026-10-12-candidate-proof"] }),
    expected,
  );
  assert.deepEqual(dated.metadata, historical.metadata);
  assert.deepEqual(dated.trees, historical.trees);
  assert.equal(historical.source_path, "submissions/candidate-proof/src");
  assert.equal(dated.source_path, "submissions/2026-10-12-candidate-proof/src");
});
test("immutable source lookup rejects duplicate dated and historical identities", async () => {
  for (const directories of [
    ["candidate-proof", "2026-10-12-candidate-proof"],
    ["2026-10-12-candidate-proof", "2026-10-13-candidate-proof"],
  ])
    await assert.rejects(
      readSubmissionSources(sourceApi({ directories }), expected),
      /Duplicate submission directories/,
    );
});
test("dated submissions resolve dated dependencies by their stable result IDs", async () => {
  const item = (path, character, type = "tree", mode = "040000") => ({
    path,
    sha: character.repeat(40),
    type,
    mode,
  });
  const blob = (value) => ({
    encoding: "base64",
    size: Buffer.byteLength(JSON.stringify(value)),
    content: Buffer.from(JSON.stringify(value)).toString("base64"),
  });
  const original = sourceApi({
    blob: blob({ ...metadata(), dependencies: ["earlier-proof"] }),
  });
  const routes = {
    ["git/trees/" + "b".repeat(40)]: {
      tree: [
        item("2026-10-12-candidate-proof", "c"),
        item("2026-10-11-earlier-proof", "2"),
      ],
    },
    ["git/trees/" + "2".repeat(40)]: {
      tree: [item("src", "d"), item("metadata.json", "3", "blob", "100644")],
    },
    ["git/blobs/" + "3".repeat(40)]: blob(metadata()),
  };
  const result = await readSubmissionSources(
    (route) =>
      routes[route.slice("repos/owner/repo/".length)] ?? original(route),
    expected,
  );
  assert.deepEqual(result.trees, {
    "candidate-proof": "c".repeat(40),
    "earlier-proof": "2".repeat(40),
  });
  assert.equal(
    result.source_path,
    "submissions/2026-10-12-candidate-proof/src",
  );
});
test("a PR metadata block or an independent receipt cannot replace the committed Lean source", async () => {
  for (const change of [
    { missingMain: true },
    { mainMode: "120000" },
    { metadataMode: "120000" },
  ])
    await assert.rejects(
      readSubmissionMetadata(sourceApi(change), expected),
      /regular submission/,
    );
});

test("immutable metadata validation requires declared dependencies to exist", async () => {
  const value = { ...metadata(), dependencies: ["missing-proof"] };
  const blob = {
    encoding: "base64",
    size: 100,
    content: Buffer.from(JSON.stringify(value)).toString("base64"),
  };
  await assert.rejects(
    readSubmissionMetadata(sourceApi({ blob }), expected),
    /regular submission missing-proof/,
  );
});
test("immutable metadata validation rejects dependency cycles", async () => {
  const value = { ...metadata(), dependencies: ["candidate-proof"] };
  const blob = {
    encoding: "base64",
    size: 100,
    content: Buffer.from(JSON.stringify(value)).toString("base64"),
  };
  await assert.rejects(
    readSubmissionMetadata(sourceApi({ blob }), expected),
    /Cyclic submission dependencies/,
  );
});

test("duplicate metadata fields cannot hide traces, including escaped keys", () => {
  for (const key of ['"agent_traces"', '"agent\\u005ftraces"']) {
    const raw =
      '{"agent_traces":[{"output":"private-credential"}],' + key + ":[]}";
    assert.throws(
      () => parseSubmissionMetadataJSON(raw),
      (error) => error.message === "Duplicate submission metadata field",
    );
  }
  const value = {
    title: "agent_traces",
    description: 'brackets {[,]}, quote \\"',
    agent_traces: [
      { agent_traces: [], child: { agent_traces: [1] } },
      { message: '"agent_traces":[], "agent_traces":[]' },
    ],
  };
  assert.deepEqual(parseSubmissionMetadataJSON(JSON.stringify(value)), value);
});

test("historical classification cannot be supplied through explicit publication metadata fields", () => {
  for (const changes of [
    { historical: true },
    { historical: false },
    { historical_date: "2026-10-08" },
  ])
    assert.throws(
      () => validateSubmissionMetadata({ ...metadata(), ...changes }),
      /Invalid publication metadata/,
    );
});
