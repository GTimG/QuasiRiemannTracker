import test from "node:test";
import assert from "node:assert/strict";
import {
  mkdtempSync,
  rmSync,
  readFileSync,
  writeFileSync,
  mkdirSync,
  symlinkSync,
} from "node:fs";
import { join } from "node:path";
import { tmpdir } from "node:os";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { registeredFixture } from "./fixtures/registered-receipt.mjs";
import {
  reusableReceipt,
  validateRegisteredAttempt,
} from "../verifier/receipt-reuse.mjs";
import { verificationResult } from "../verifier/actions/result.mjs";
const fixture = (t) => {
  const root = mkdtempSync(join(tmpdir(), "qrh-receipt-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  return { root, ...registeredFixture(root) };
};

test("approved receipt survives fresh source preparation and preserves first verification date", (t) => {
  const f = fixture(t),
    prepared = structuredClone(f.contract);
  prepared.library_inventory_sha256 = "0".repeat(64); // source-only preparation
  const r = reusableReceipt(f.root, f.expected, { prepared });
  assert.deepEqual(r.registration, f.registration);
  assert.equal(
    verificationResult(f.root, f.expected, f.attempt()).verified_at,
    "2026-10-13T00:00:00Z",
  );
});
test("missing approval falls back to full verification; candidate files cannot approve themselves", (t) => {
  const f = fixture(t);
  mkdirSync(join(f.root, "submissions/candidate-proof/verifier"), {
    recursive: true,
  });
  f.write("submissions/candidate-proof/verifier/local-results.json", [
    f.registration,
  ]);
  f.write("verifier/local-results.json", []);
  assert.equal(
    reusableReceipt(f.root, f.expected, { prepared: f.contract }),
    null,
  );
  assert.throws(
    () => validateRegisteredAttempt(f.root, f.expected, f.attempt(), "success"),
    /exact PR head/,
  );
});
for (const key of [
  "head_sha",
  "repository",
  "number",
  "theta_exact",
  "result_id",
])
  test(`cannot reuse a receipt after ${key} changes`, (t) => {
    const f = fixture(t),
      expected = { ...f.expected, [key]: key === "number" ? 99 : "changed" };
    assert.equal(reusableReceipt(f.root, expected), null);
    assert.throws(
      () => validateRegisteredAttempt(f.root, expected, f.attempt(), "success"),
      /exact PR head/,
    );
  });
test("duplicate approvals are rejected", (t) => {
  const f = fixture(t);
  f.write("verifier/local-results.json", [f.registration, f.registration]);
  assert.throws(() => reusableReceipt(f.root, f.expected), /exact PR head/);
});
test("tampered receipt bytes are rejected", (t) => {
  const f = fixture(t);
  f.write(`${f.dir}/result.json`, { ...f.report, status: "FAIL" });
  assert.throws(() => reusableReceipt(f.root, f.expected), /receipt bytes/);
});
for (const [key, value] of [
  ["status", "FAIL"],
  ["targets", ["Candidate.bound"]],
  ["kernels", ["Lean default"]],
  ["allowed_axioms", ["propext", "Classical.choice", "Quot.sound", "sorryAx"]],
  [
    "allowed_axioms",
    ["propext", "Classical.choice", "Quot.sound", "Hidden.assumption"],
  ],
  ["sandbox_preflight", "FAIL"],
  ["candidate_mount_preflight", "FAIL"],
  ["challenge_exported_before_candidate_execution", false],
  ["receipt_outside_candidate", false],
  ["judge_exit_code", 1],
  ["reviewed_pr_head", "c".repeat(40)],
])
  test(`a registered hash does not excuse invalid proof evidence: ${key} ${JSON.stringify(value)}`, (t) => {
    const f = fixture(t);
    f.report[key] = value;
    f.seal();
    assert.throws(
      () => reusableReceipt(f.root, f.expected),
      /canonical bound with all three kernels/,
    );
  });
for (const path of [
  "verifier/pins.json",
  "verifier/challenge.mjs",
  "verifier/standard/tool-pins.json",
  ".github/workflows/pr-admission.yml",
  "package-lock.json",
])
  test(`changed policy invalidates approval: ${path}`, (t) => {
    const f = fixture(t);
    writeFileSync(
      join(f.root, path),
      readFileSync(join(f.root, path), "utf8") + "\n",
    );
    assert.throws(
      () => reusableReceipt(f.root, f.expected),
      /verifier policy changed/,
    );
    assert.throws(
      () =>
        verificationResult(f.root, f.expected, {
          ...f.expected,
          status: "resource-exhausted",
        }),
      /suitable worker/,
    );
  });
test("checker or library replacement invalidates runtime approval", (t) => {
  const f = fixture(t);
  f.report.tool_pins.judge_nanoda_bin = "0".repeat(64);
  f.seal();
  assert.throws(() => reusableReceipt(f.root, f.expected), /reviewed runtime/);
});
for (const key of [
  "source_files",
  "submission_trees",
  "generated_files",
  "manifest",
])
  test(`fresh source preparation rejects modified ${key}`, (t) => {
    const f = fixture(t),
      prepared = structuredClone(f.contract);
    prepared[key] = {};
    assert.throws(
      () => reusableReceipt(f.root, f.expected, { prepared }),
      /fresh immutable source/,
    );
  });
test("receipt cannot weaken the canonical statement or substitute the constant", (t) => {
  const f = fixture(t);
  f.contract.generated_files["Challenge.lean"] = "0".repeat(64);
  f.seal();
  assert.throws(
    () => reusableReceipt(f.root, f.expected),
    /canonical challenge/,
  );
  f.contract.manifest.theta.numerator = "2";
  f.seal();
  assert.throws(() => reusableReceipt(f.root, f.expected), /contract bound/);
});
test("adversarial controls must have actually rejected the bad statements/proofs", (t) => {
  const f = fixture(t);
  f.controls[1].exit_code = 0;
  f.seal();
  assert.throws(
    () => reusableReceipt(f.root, f.expected),
    /adversarial controls/,
  );
});
test("public contract and dependency evidence cannot be substituted", (t) => {
  const f = fixture(t);
  f.write(`${f.dir}/contract.json`, {});
  assert.throws(() => reusableReceipt(f.root, f.expected), /contract hash/);
  f.seal();
  f.write(`${f.dir}/dependency-pins.json`, {});
  assert.throws(
    () => reusableReceipt(f.root, f.expected),
    /dependency revisions/,
  );
});
for (const path of [
  "verifier/standard/receipts/../result.json",
  "submissions/candidate-proof/result.json",
])
  test(`untrusted receipt path is rejected: ${path}`, (t) => {
    const f = fixture(t);
    f.registration.report_url = `https://github.com/${f.expected.repository}/blob/${"b".repeat(40)}/${path}`;
    f.seal();
    assert.throws(
      () => reusableReceipt(f.root, f.expected),
      /protected evidence path/,
    );
  });
test("symlink receipt cannot escape the protected evidence directory", (t) => {
  const f = fixture(t),
    path = join(f.root, f.dir, "result.json");
  rmSync(path);
  symlinkSync(join(f.root, "package.json"), path);
  assert.throws(() => reusableReceipt(f.root, f.expected), /symlink evidence/);
});
test("failed receipt job and forged worker markers cannot publish", (t) => {
  const f = fixture(t);
  assert.throws(
    () => verificationResult(f.root, f.expected, f.attempt(), "failure"),
    /job did not complete/,
  );
  for (const key of ["registration_sha256", "source_contract_sha256"])
    assert.throws(
      () =>
        verificationResult(f.root, f.expected, {
          ...f.attempt(),
          [key]: "0".repeat(64),
        }),
      /worker record differs/,
    );
  assert.throws(
    () =>
      verificationResult(f.root, f.expected, {
        ...f.attempt(),
        status: "invalid-receipt",
        reason: "tampered",
      }),
    /tampered/,
  );
});
test("receipt action skips all external checker execution and reads no candidate cache", (t) => {
  const f = fixture(t);
  mkdirSync(join(f.root, "verification-context"));
  mkdirSync(join(f.root, "verification/prepared"), { recursive: true });
  mkdirSync(join(f.root, "verification/candidate-lib"));
  f.write("verification/candidate-lib/result.json", {
    status: "PASS",
    allowed_axioms: ["sorryAx"],
  });
  f.write("verification-context/context.json", { expected: f.expected });
  f.write("verification/prepared/contract.json", f.contract);
  const result = spawnSync(
    process.execPath,
    [
      fileURLToPath(
        new URL("../verifier/actions/reuse-receipt.mjs", import.meta.url),
      ),
    ],
    {
      cwd: f.root,
      encoding: "utf8",
      env: { PATH: "/no-tools", GITHUB_OUTPUT: join(f.root, "outputs") },
    },
  );
  assert.equal(result.status, 0, result.stderr);
  assert.equal(readFileSync(join(f.root, "outputs"), "utf8"), "reused=true\n");
  assert.deepEqual(
    JSON.parse(readFileSync(join(f.root, "verification/attempt.json"))),
    f.attempt(),
  );
});
test("receipt reuse precedes provisioning and retains protected orchestration and read-only workers", () => {
  const workflow = readFileSync(
    new URL("../.github/workflows/pr-admission.yml", import.meta.url),
    "utf8",
  );
  const worker = workflow.split("  verify:\n")[1].split("  admission:\n")[0];
  assert.match(worker, /ref: \$\{\{ github\.workflow_sha \}\}/);
  assert.match(worker, /contents: read/);
  assert.doesNotMatch(worker, /contents: write/);
  assert.ok(
    worker.indexOf("verifier/actions/prepare.mjs") <
      worker.indexOf("verifier/actions/reuse-receipt.mjs"),
  );
  assert.ok(
    worker.indexOf("verifier/actions/reuse-receipt.mjs") <
      worker.indexOf("verifier-cache"),
  );
  for (const label of [
    "Restore the shared checking environment",
    "Install worker prerequisites",
  ]) {
    const step = worker.split(`- name: ${label}\n`)[1].split("\n      - ")[0];
    assert.match(
      step,
      /steps\.receipt\.outcome == 'success' && steps\.receipt\.outputs\.reused != 'true'/,
    );
  }
  assert.match(
    worker,
    /steps\.check\.outcome != 'success' && !\(steps\.receipt\.outcome == 'success' && steps\.receipt\.outputs\.reused == 'true'\)/,
  );
  assert.match(
    worker,
    /QRH_CHECK_RESULT:.*steps\.receipt\.outcome == 'success' && steps\.receipt\.outputs\.reused == 'true' && 'success'/,
  );
});
