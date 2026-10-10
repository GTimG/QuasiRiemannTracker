import test from "node:test";
import assert from "node:assert/strict";
import {
  cpSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
  symlinkSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { createHash } from "node:crypto";
import {
  CYCLE25_ID,
  CYCLE25_PIN,
  validateCycle25KernelEvidence,
} from "../core/cycle25-kernel-evidence.mjs";
const sha = (data) => createHash("sha256").update(data).digest("hex");
const read = (path) => JSON.parse(readFileSync(path, "utf8"));
const data = () => read("catalogue/results.json");
const record = (d) => d.records.find((r) => r.id === CYCLE25_ID);
function copy() {
  const root = mkdtempSync(join(tmpdir(), "cycle25-acceptance-"));
  for (const path of [
    `proofs/${CYCLE25_ID}`,
    "verifier/cycle25",
    CYCLE25_PIN.directory,
  ]) {
    mkdirSync(dirname(join(root, path)), { recursive: true });
    cpSync(path, join(root, path), { recursive: true });
  }
  return root;
}
test("Cycle25 requires the independent eight-target acceptance and complete pinned source", () => {
  const d = data();
  const receipt = validateCycle25KernelEvidence(process.cwd(), d);
  assert.equal(receipt.candidate_modules_rebuilt, 3224);
  assert.equal(receipt.targets.length, 8);
  assert.ok(receipt.targets.includes("QRHBoundsPR9.quarticRootExistsUnique"));
  assert.equal(receipt.verified_at, record(d).timeline_at);
  assert.equal(
    receipt.source_commit,
    "58344dfdbe756cf2f743da1908ffe0582418cf5b",
  );
  assert.equal(receipt.receipt_outside_candidate, true);
  assert.equal(
    read("public/proofs/cycle25-quartic-20261010/collection.json").status,
    "verification-pending",
  );
});
test("pending contributor reports cannot self-approve or mint an independent date", () => {
  const d = data(),
    r = record(d);
  r.status = "verification-pending";
  assert.throws(
    () => validateCycle25KernelEvidence(process.cwd(), d),
    /pending contribution has/,
  );
  r.first_verified_at = "";
  assert.equal(validateCycle25KernelEvidence(process.cwd(), d), null);
  r.status = "verified";
  assert.throws(
    () => validateCycle25KernelEvidence(process.cwd(), d),
    /independent sandboxed acceptance/,
  );
  for (const mutate of [
    (r) => (r.source_commit = "0".repeat(40)),
    (r) => (r.theta.numerator = "1"),
    (r) => (r.first_verified_at = "2026-10-10T11:43:39Z"),
    (r) => (r.builds_on = ["openai-baseline"]),
    (r) => (r.pr = 7),
  ]) {
    const d = data();
    mutate(record(d));
    assert.throws(
      () => validateCycle25KernelEvidence(process.cwd(), d),
      /revision differs|bound differs|timeline must use|predecessors differ/,
    );
  }
});
test("changing source or the runner invalidates the prior receipt even after submitted hashes change", () => {
  const root = copy();
  try {
    for (const path of [
      `proofs/${CYCLE25_ID}/formalization/Cycle25/Assembly/Final/Endpoint.lean`,
      "verifier/cycle25/replay.py",
      "verifier/cycle25/pins.json",
    ]) {
      const file = join(root, path),
        original = readFileSync(file);
      writeFileSync(file, Buffer.concat([original, Buffer.from("\n")]));
      assert.throws(
        () => validateCycle25KernelEvidence(root, data()),
        /checked source changed|current replay differs/,
      );
      writeFileSync(file, original);
    }
    // Candidate-generated manifests are not the protected source binding.
    const file = join(
      root,
      `proofs/${CYCLE25_ID}/formalization/Cycle25/Assembly/Final/Endpoint.lean`,
    );
    writeFileSync(
      file,
      readFileSync(file, "utf8") + "\n-- modified after verification\n",
    );
    writeFileSync(
      join(root, `proofs/${CYCLE25_ID}.sha256.json`),
      JSON.stringify({
        "formalization/Cycle25/Assembly/Final/Endpoint.lean": sha(
          readFileSync(file),
        ),
      }),
    );
    assert.throws(
      () => validateCycle25KernelEvidence(root, data()),
      /checked source changed.*re-verification required/,
    );
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});
test("forged or incomplete receipts, unsafe evidence and extra assumptions fail closed", () => {
  const root = copy(),
    directory = join(root, CYCLE25_PIN.directory);
  const originalReceipt = readFileSync(join(directory, "result.json"));
  const originalCollection = readFileSync(join(directory, "collection.json"));
  try {
    writeFileSync(join(directory, "result.json"), "{}");
    assert.throws(
      () => validateCycle25KernelEvidence(root, data()),
      /artifact checksum mismatch/,
    );
    writeFileSync(join(directory, "result.json"), originalReceipt);
    for (const [change, pattern] of [
      [(r) => (r.status = "timed-out"), /no checker acceptance/],
      [(r) => r.allowed_axioms.push("sorryAx"), /axiom scope/],
      [(r) => r.kernels.pop(), /kernel or axiom scope/],
      [
        (r) =>
          (r.targets = r.targets.filter(
            (n) => !n.endsWith("quarticRootExistsUnique"),
          )),
        /target scope/,
      ],
      [
        (r) => (r.receipt_outside_candidate = false),
        /isolation or challenge ordering/,
      ],
      [
        (r) => (r.challenge_exported_before_candidate_execution = false),
        /isolation or challenge ordering/,
      ],
      [(r) => (r.candidate_modules_rebuilt = 301), /build scope/],
      [(r) => (r.source_commit = "0".repeat(40)), /source revision differs/],
      [
        (r) => (r.reviewed_pr_head = "0".repeat(40)),
        /reviewed revision differs/,
      ],
    ]) {
      const report = JSON.parse(originalReceipt),
        collection = JSON.parse(originalCollection),
        pin = structuredClone(CYCLE25_PIN);
      change(report);
      const bytes = JSON.stringify(report);
      writeFileSync(join(directory, "result.json"), bytes);
      collection.files["result.json"] = pin.receipt_sha256 = sha(bytes);
      const manifest = JSON.stringify(collection);
      writeFileSync(join(directory, "collection.json"), manifest);
      pin.collection_sha256 = sha(manifest);
      // Even recomputed wrappers cannot conceal an invalid acceptance scope.
      assert.throws(
        () => validateCycle25KernelEvidence(root, data(), pin),
        pattern,
      );
    }
    writeFileSync(join(directory, "result.json"), originalReceipt);
    writeFileSync(join(directory, "collection.json"), originalCollection);
    writeFileSync(join(directory, "unlisted.json"), "{}");
    assert.throws(
      () => validateCycle25KernelEvidence(root, data()),
      /unlisted or missing/,
    );
    rmSync(join(directory, "unlisted.json"));
    symlinkSync("result.json", join(directory, "link.json"));
    assert.throws(() => validateCycle25KernelEvidence(root, data()), /symlink/);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});
