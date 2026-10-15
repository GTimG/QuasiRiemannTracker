import test from "node:test";
import assert from "node:assert/strict";
import {
  parseSubmissionMetadata,
  readSubmissionMetadata,
  validateSubmissionMetadata,
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

function sourceApi({
  missingMain = false,
  mainMode = "100644",
  metadataMode = "100644",
  blob = null,
} = {}) {
  const item = (path, sha, type = "tree", mode = "040000") => ({
    path,
    sha: sha.repeat(40),
    type,
    mode,
  });
  const routes = {
    ["git/trees/" + "a".repeat(40)]: { tree: [item("submissions", "b")] },
    ["git/trees/" + "b".repeat(40)]: { tree: [item("candidate-proof", "c")] },
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
