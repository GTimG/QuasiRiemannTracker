import test from "node:test";
import assert from "node:assert/strict";
import { readdirSync } from "node:fs";
import {
  dependencyGraph,
  submissionDependencies,
} from "../verifier/submission-dependencies.mjs";
import { submissionFiles } from "../verifier/manifest.mjs";
function input(dependencies, sources) {
  return {
    files: [
      {
        path: "metadata.json",
        bytes: Buffer.from(JSON.stringify({ dependencies })),
      },
      ...Object.entries(sources).map(([module, source]) => ({
        path: "src/" + module.replaceAll(".", "/") + ".lean",
        bytes: Buffer.from(source),
      })),
    ],
  };
}
function fixture() {
  return {
    "first-proof": input([], {
      "Candidate.Main": "import Submissions.first_proof.Main",
      "Submissions.first_proof.Main": "import Mathlib",
      "Submissions.first_proof.Helper": "import Mathlib",
    }),
    "second-proof": input(["first-proof"], {
      "Candidate.Main": "import Submissions.second_proof.Main",
      "Submissions.second_proof.Main": "import Submissions.first_proof.Helper",
    }),
    "third-proof": input(["second-proof"], {
      "Candidate.Main": "import Submissions.third_proof.Main",
      "Submissions.third_proof.Main": "import Submissions.second_proof.Main",
    }),
  };
}
test("builds transitive imports in order without including dependency entrypoint wrappers", () => {
  const sources = fixture();
  const g = dependencyGraph("third-proof", (id) => sources[id]);
  assert.deepEqual(g.order, [
    "Submissions.first_proof.Helper",
    "Submissions.second_proof.Main",
    "Submissions.third_proof.Main",
    "Candidate.Main",
  ]);
  assert.equal(g.submissions.size, 3);
  assert.equal(g.modules.get("Candidate.Main").owner, "third-proof");
});
test("rejects undeclared and missing imports, including undeclared transitive dependencies", () => {
  const sources = fixture();
  sources["third-proof"].files.at(-1).bytes = Buffer.from(
    "import Submissions.first_proof.Helper",
  );
  assert.throws(
    () => dependencyGraph("third-proof", (id) => sources[id]),
    /Undeclared dependency/,
  );
  sources["third-proof"].files.at(-1).bytes = Buffer.from(
    "import Submissions.first_proof.Missing",
  );
  assert.throws(
    () => dependencyGraph("third-proof", (id) => sources[id]),
    /Missing submission module/,
  );
});
test("rejects dependency cycles, source ownership conflicts and external OAI imports", () => {
  const sources = fixture();
  sources["first-proof"].files[0].bytes = Buffer.from(
    '{"dependencies":["third-proof"]}',
  );
  assert.throws(
    () => dependencyGraph("third-proof", (id) => sources[id]),
    /Cyclic submission/,
  );
  sources["first-proof"].files[0].bytes = Buffer.from("{}");
  sources["first-proof"].files.push({
    path: "src/Submissions/second_proof/Other.lean",
    bytes: Buffer.from(""),
  });
  assert.throws(
    () => dependencyGraph("third-proof", (id) => sources[id]),
    /must belong/,
  );
  sources["first-proof"].files.pop();
  sources["first-proof"].files.at(-1).bytes = Buffer.from(
    "import OAI.NumberTheory.DirichletL.Nonvanishing",
  );
  assert.throws(
    () => dependencyGraph("third-proof", (id) => sources[id]),
    /Import OAI source through/,
  );
});
test("validates source revision IDs and uniqueness", () => {
  for (const dependencies of [
    ["../escape"],
    ["first-proof", "first-proof"],
    "first-proof",
  ])
    assert.throws(
      () => submissionDependencies({ dependencies }),
      /Invalid submission dependencies/,
    );
});
test("every repository submission resolves its complete import closure", () => {
  const cache = new Map();
  const load = (id) => {
    if (!cache.has(id)) cache.set(id, submissionFiles(`submissions/${id}`));
    return cache.get(id);
  };
  for (const id of readdirSync("submissions")) {
    const g = dependencyGraph(id, load);
    assert.equal(g.order.at(-1), "Candidate.Main");
  }
});
