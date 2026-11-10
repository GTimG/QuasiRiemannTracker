import test from "node:test";
import assert from "node:assert/strict";
import {
  mkdtempSync,
  mkdirSync,
  writeFileSync,
  rmSync,
  symlinkSync,
  readdirSync,
  readFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  readSubmissions,
  buildSubmissionCatalogue,
} from "../scripts/submission-catalogue.mjs";
import { exactBound } from "../core/exact-bound.mjs";
import { standardChallenge } from "../core/standard-challenge.mjs";
import {
  submissionDirectory,
  validateSubmissionDirectory,
} from "../verifier/submission-paths.mjs";

const metadata = {
  title: "Bound",
  authors: [{ name: "Author" }],
  description: "Proof and attribution.",
};
function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), "qrh-layout-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const dir = join(root, "submissions/2026-10-27-example-proof");
  mkdirSync(join(dir, "src/Candidate"), { recursive: true });
  writeFileSync(join(dir, "src/Candidate/Main.lean"), "import Mathlib\n");
  writeFileSync(join(dir, "metadata.json"), JSON.stringify(metadata));
  return { root, dir };
}
for (const file of ["metadata.json", "src/Candidate/Main.lean"]) {
  test(`deployment rejects a submission missing ${file}, including offline builds`, (t) => {
    const { root, dir } = fixture(t);
    rmSync(join(dir, file));
    assert.throws(
      () => buildSubmissionCatalogue({ root }),
      /Missing (metadata.json|src\/Candidate\/Main.lean)/,
    );
  });
  test(`deployment rejects a symlink at ${file}`, (t) => {
    const { root, dir } = fixture(t);
    rmSync(join(dir, file));
    symlinkSync("/dev/null", join(dir, file));
    assert.throws(() => readSubmissions(root), /regular files/);
  });
}
test("deployment rejects symlinked supporting modules and submission directories", (t) => {
  const { root, dir } = fixture(t);
  symlinkSync("/dev/null", join(dir, "src/Candidate/Helper.lean"));
  assert.throws(() => readSubmissions(root), /regular files/);
  rmSync(join(dir, "src/Candidate/Helper.lean"));
  symlinkSync(dir, join(root, "submissions/another-proof"));
  assert.throws(() => readSubmissions(root), /regular directories/);
});
test("every retained revision has a dated directory, colocated metadata and complete standard source layout", () => {
  const submissions = readSubmissions(process.cwd());
  const directories = readdirSync("submissions");
  for (const directory of directories)
    assert.equal(validateSubmissionDirectory(directory), directory);
  for (const id of [
    "akashlevy-20261009-weighted-numerator",
    "argonaut-20261008",
    "liu-20261008",
    "cycle25-quartic-20261010",
    "proofcouncil-20261009",
    "nielstron-20261009-tightening",
    "nielstron-algebraic-20261009",
  ])
    assert.ok(submissions.has(id));
  for (const [id] of submissions) {
    assert.ok(
      readFileSync(
        `submissions/${submissionDirectory(id, directories)}/src/Candidate/Main.lean`,
        "utf8",
      ).includes("bound"),
    );
  }
  assert.ok(!readdirSync(process.cwd()).includes("proofs"));
});
test("the algebraic profile generates a fixed exact statement and rejects Lean injection", () => {
  const bound = exactBound("(1507 − 2√921) / 1653");
  assert.match(
    standardChallenge(bound.theta, bound.exact_bound),
    /1507 - 2 \* Real.sqrt 921/,
  );
  const liu_b2 = exactBound("(777 − √1081) / 852");
  assert.match(
    standardChallenge(liu_b2.theta, liu_b2.exact_bound),
    /\(777 - Real\.sqrt 1081\) \/ 852/,
  );
  for (const invalid of [
    "Real.sqrt 921",
    "1/1) := by trivial",
    "(1507 − 2√922) / 1653",
    "(777 − √1082) / 852",
  ]) {
    assert.throws(() => exactBound(invalid), /checking profile/);
  }
});

test("metadata changes are included in the authenticated submission inventory", async (t) => {
  const { submissionFiles } = await import("../verifier/manifest.mjs");
  const { dir } = fixture(t);
  const before = submissionFiles(dir).inventory;
  writeFileSync(
    join(dir, "metadata.json"),
    JSON.stringify({ ...metadata, title: "Corrected title" }),
  );
  const after = submissionFiles(dir).inventory;
  assert.notEqual(
    before.find((f) => f.path === "metadata.json").sha256,
    after.find((f) => f.path === "metadata.json").sha256,
  );
  assert.equal(
    before.find((f) => f.path.endsWith("Main.lean")).sha256,
    after.find((f) => f.path.endsWith("Main.lean")).sha256,
  );
});

test("embedded traces retain exact metadata bytes and source inventory binding", async (t) => {
  const { submissionFiles } = await import("../verifier/manifest.mjs");
  const { dir } = fixture(t);
  const before = submissionFiles(dir);
  const bytes = Buffer.from(
    JSON.stringify(
      {
        ...metadata,
        agent_traces: [{ output: "x".repeat(70 * 1024) }],
      },
      null,
      2,
    ) + "\n",
  );
  writeFileSync(join(dir, "metadata.json"), bytes);
  const after = submissionFiles(dir);
  assert.deepEqual(
    after.files.find((file) => file.path === "metadata.json").bytes,
    bytes,
  );
  assert.notDeepEqual(after.inventory, before.inventory);
  assert.equal(
    after.inventory.find((file) => file.path.endsWith("Main.lean")).sha256,
    before.inventory.find((file) => file.path.endsWith("Main.lean")).sha256,
  );
  writeFileSync(
    join(dir, "metadata.json"),
    '{"agent_traces":[{"secret":"private-credential" INVALID}]}',
  );
  assert.throws(
    () => submissionFiles(dir),
    (error) =>
      error.message === "Submission metadata must contain valid UTF-8 JSON",
  );
});
