import test from "node:test";
import assert from "node:assert/strict";
import {
  mkdtempSync,
  mkdirSync,
  writeFileSync,
  rmSync,
  readFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { certificate, workerCertificate } from "../verifier/certificate.mjs";
import { validateAdmission } from "../verifier/pr-evidence.mjs";
import { submission } from "../verifier/manifest.mjs";
const expected = {
  repository: "owner/repo",
  number: 42,
  head_sha: "a".repeat(40),
  result_id: "test-bound",
  theta_exact: "1/1",
};
const report = { verified_at: "2026-10-13T00:00:00Z" };
const record = () =>
  workerCertificate(
    expected,
    report,
    "https://github.com/owner/repo/actions/runs/123/attempts/1",
    Buffer.from(JSON.stringify(report)),
  );
test("minimal verification records bind source, exact bound, date and report", () => {
  const c = record();
  assert.equal(c.source_commit, expected.head_sha);
  assert.equal(c.theta_exact, expected.theta_exact);
  assert.equal(c.verified_at, report.verified_at);
  assert.equal(c.report_sha256.length, 64);
  for (const change of [
    { source_commit: "main" },
    { report_url: "https://github.com/owner/repo/blob/main/report.json" },
    { kernels: ["Lean default"] },
    { verified_at: "invalid" },
    { report_sha256: "" },
  ])
    assert.throws(
      () => certificate({ ...c, ...change }),
      /Invalid verification record/,
    );
});
test("local fallback matches the exact PR head and declared bound on the base branch", (t) => {
  const root = mkdtempSync(join(tmpdir(), "qrh-certificate-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  mkdirSync(join(root, "verifier"));
  const entry = { ...record(), ...expected };
  const save = (entries) =>
    writeFileSync(
      join(root, "verifier/local-results.json"),
      JSON.stringify(entries),
    );
  save([entry]);
  assert.deepEqual(validateAdmission(root, expected), entry);
  for (const key of [
    "repository",
    "number",
    "head_sha",
    "result_id",
    "theta_exact",
  ])
    assert.throws(
      () => validateAdmission(root, { ...expected, [key]: "different" }),
      /exact PR head/,
    );
  save([entry, entry]);
  assert.throws(() => validateAdmission(root, expected), /exact PR head/);
  save([{ ...entry, source_commit: "b".repeat(40) }]);
  assert.throws(() => validateAdmission(root, expected), /source differs/);
});
test("submission layout contains Lean source with a fixed entrypoint", (t) => {
  const root = mkdtempSync(join(tmpdir(), "qrh-lean-only-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  mkdirSync(join(root, "src/Candidate"), { recursive: true });
  writeFileSync(join(root, "src/Candidate/Main.lean"), "import Mathlib\n");
  writeFileSync(
    join(root, "metadata.json"),
    JSON.stringify({
      title: "Test",
      authors: [{ name: "Author" }],
      description: "A proof.",
    }),
  );
  const declaration = {
    id: "test-bound",
    theta: { numerator: "1", denominator: "1" },
    entrypoint: { module: "Bad", declaration: "Bad" },
  };
  assert.deepEqual(submission(root, declaration).manifest.entrypoint, {
    module: "Candidate.Main",
    declaration: "Candidate.bound",
  });
  writeFileSync(join(root, "manifest.json"), "{}");
  assert.throws(
    () => submission(root, declaration),
    /metadata.json and Lean source/,
  );
});

test("the certificate hash authenticates the exact archived report bytes", () => {
  assert.throws(
    () =>
      workerCertificate(
        expected,
        report,
        record().report_url,
        Buffer.from("{}"),
      ),
    /Archived report differs/,
  );
});
