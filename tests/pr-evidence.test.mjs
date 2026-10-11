import test from "node:test";
import assert from "node:assert/strict";
import {
  cpSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { createHash } from "node:crypto";
import { validateAdmission } from "../verifier/pr-evidence.mjs";

const read = (path) => JSON.parse(readFileSync(path, "utf8"));
const pin = read("core/cycle25-kernel-pins.json");
const receipt = read(`${pin.directory}/result.json`);
const expected = {
  repository: "GTimG/QuasiRiemannTracker",
  number: 9,
  head_sha: receipt.reviewed_pr_head,
  result_id: "cycle25-quartic-20261010",
  theta_exact: receipt.theta_exact,
};
const approval = () => ({
  ...expected,
  pin: structuredClone(pin),
  contribution: {
    repository: "HaileyStorm/QuasiRiemannTracker",
    source_commit: receipt.source_commit,
    source_compiler: receipt.source_compiler,
    judge_toolchain: receipt.judge_toolchain,
    palomar_commit: receipt.verifier_commit,
  },
});
function writePolicy(root, admissions) {
  mkdirSync(join(root, "verifier"), { recursive: true });
  writeFileSync(
    join(root, "verifier/pr-admissions.json"),
    JSON.stringify({ schema_version: 1, admissions }),
  );
}
function fixture(t, entry = approval(), evidence = true) {
  const root = mkdtempSync(join(tmpdir(), "qrh-pr-admission-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  writePolicy(root, entry ? [entry] : []);
  if (evidence) {
    for (const [source, destination] of [
      ["verifier/cycle25", "verifier/cycle25"],
      [pin.directory, entry?.pin.directory ?? pin.directory],
    ]) {
      mkdirSync(dirname(join(root, destination)), { recursive: true });
      cpSync(source, join(root, destination), { recursive: true });
    }
  }
  return root;
}

test("a pinned independent three-kernel receipt admits its exact PR head and bound", (t) => {
  const root = fixture(t);
  const result = validateAdmission(root, expected);
  assert.deepEqual(result.kernels, ["Lean default", "nanoda", "con-ron"]);
  assert.equal(result.reviewed_pr_head, expected.head_sha);
  assert.equal(result.theta_exact, expected.theta_exact);
});

test("separate evidence PRs may archive the same authenticated dossier outside proof paths", (t) => {
  const entry = approval();
  entry.pin.directory = "evidence/pr-checks/cycle25-acceptance";
  const root = fixture(t, entry);
  assert.equal(validateAdmission(root, expected).status, "PASS");
});

test("empty trusted admissions reject candidate-authored PASS reports", (t) => {
  const root = fixture(t, null, false);
  mkdirSync(join(root, "proofs/candidate/evidence"), { recursive: true });
  writeFileSync(
    join(root, "proofs/candidate/evidence/result.json"),
    JSON.stringify({ ...receipt, status: "PASS" }),
  );
  assert.throws(
    () => validateAdmission(root, expected),
    /archive an independent maintainer replay/,
  );
});

test("requires receipt identity to match the head, bound, result, PR and repository", (t) => {
  const root = fixture(t, approval(), false);
  for (const change of [
    { head_sha: "0".repeat(40) },
    { theta_exact: "7/8" },
    { result_id: "other-result" },
    { number: 15 },
    { repository: "Someone/QuasiRiemannTracker" },
  ])
    assert.throws(
      () => validateAdmission(root, { ...expected, ...change }),
      /archive an independent maintainer replay/,
    );
});

test("requires receipt proof to match the approval head and bound", (t) => {
  const entry = approval();
  const root = fixture(t, entry);
  for (const [change, pattern] of [
    [{ head_sha: "0".repeat(40) }, /receipt must verify this exact PR head/],
    [{ theta_exact: "7/8" }, /receipt must verify the declared exact bound/],
  ]) {
    writePolicy(root, [{ ...entry, ...change }]);
    assert.throws(
      () => validateAdmission(root, { ...expected, ...change }),
      pattern,
    );
  }
});

test("rejects invalid or duplicate trusted identities", (t) => {
  const entry = approval();
  const root = fixture(t, entry, false);
  for (const change of [
    { repository: "../repository" },
    { number: 0 },
    { head_sha: "short" },
    { result_id: "../result" },
    { theta_exact: "" },
    { theta_exact: "7/8\n" },
  ]) {
    writePolicy(root, [{ ...entry, ...change }]);
    assert.throws(
      () => validateAdmission(root, expected),
      /invalid admission identity/,
    );
  }
  for (const extra of [entry, { ...entry, theta_exact: "7/8" }]) {
    writePolicy(root, [entry, extra]);
    assert.throws(
      () => validateAdmission(root, expected),
      /duplicate admission identity/,
    );
  }
  writePolicy(root, [{ ...entry, ignored: "field" }]);
  assert.throws(
    () => validateAdmission(root, expected),
    /invalid admission entry/,
  );
});

test("rejects evidence changed after the collection was pinned", (t) => {
  const root = fixture(t);
  writeFileSync(join(root, pin.directory, "result.json"), "{}");
  assert.throws(
    () => validateAdmission(root, expected),
    /artifact checksum mismatch/,
  );
});

test("checks kernel and statement scope after authenticating checksums", (t) => {
  const entry = approval();
  const root = fixture(t, entry);
  const collection = read(join(root, pin.directory, "collection.json"));
  const sha = (bytes) => createHash("sha256").update(bytes).digest("hex");
  for (const [change, pattern] of [
    [(r) => (r.status = "verification-pending"), /no checker acceptance/],
    [(r) => r.kernels.pop(), /kernel or axiom scope differs/],
    [(r) => r.allowed_axioms.push("sorryAx"), /kernel or axiom scope differs/],
    [(r) => r.targets.shift(), /target scope differs/],
    [
      (r) => (r.challenge_exported_before_candidate_execution = false),
      /isolation or challenge ordering/,
    ],
  ]) {
    const modifiedReceipt = structuredClone(receipt);
    change(modifiedReceipt);
    const receiptBytes = JSON.stringify(modifiedReceipt);
    const modifiedCollection = structuredClone(collection);
    const modifiedEntry = approval();
    modifiedCollection.files["result.json"] = modifiedEntry.pin.receipt_sha256 =
      sha(receiptBytes);
    const collectionBytes = JSON.stringify(modifiedCollection);
    modifiedEntry.pin.collection_sha256 = sha(collectionBytes);
    writeFileSync(join(root, pin.directory, "result.json"), receiptBytes);
    writeFileSync(
      join(root, pin.directory, "collection.json"),
      collectionBytes,
    );
    writePolicy(root, [modifiedEntry]);
    assert.throws(() => validateAdmission(root, expected), pattern);
  }
});
