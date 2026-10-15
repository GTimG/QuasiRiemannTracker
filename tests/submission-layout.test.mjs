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
  reconcileAdmissions,
} from "../scripts/reconcile-admissions.mjs";
import { exactBound } from "../core/exact-bound.mjs";
import { standardChallenge } from "../core/standard-challenge.mjs";

const metadata = {
  title: "Bound",
  authors: [{ name: "Author" }],
  description: "Proof and attribution.",
};
function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), "qrh-layout-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const dir = join(root, "submissions/example-proof");
  mkdirSync(join(dir, "src/Candidate"), { recursive: true });
  writeFileSync(join(dir, "src/Candidate/Main.lean"), "import Mathlib\n");
  writeFileSync(join(dir, "metadata.json"), JSON.stringify(metadata));
  return { root, dir };
}
for (const file of ["metadata.json", "src/Candidate/Main.lean"]) {
  test(`deployment rejects a submission missing ${file}, including offline builds`, async (t) => {
    const { root, dir } = fixture(t);
    rmSync(join(dir, file));
    await assert.rejects(
      reconcileAdmissions({ root }),
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
  assert.throws(() => readSubmissions(root), /Invalid submission directory/);
});
test("every retained revision has colocated metadata and a complete standard source layout", () => {
  const submissions = readSubmissions(process.cwd());
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
        `submissions/${id}/src/Candidate/Main.lean`,
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
  for (const invalid of [
    "Real.sqrt 921",
    "1/1) := by trivial",
    "(1507 − 2√922) / 1653",
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
