import { findProofRevision } from "../core/catalogue-revisions.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync, writeFileSync, mkdtempSync, cpSync, rmSync } from "node:fs";
import { createHash } from "node:crypto";
import { tmpdir } from "node:os";
import { resolve, join } from "node:path";
import {
  validateAlgebraicKernelEvidence,
  NATIVE_ID,
  KERNEL_DIRECTORY,
} from "../core/algebraic-kernel-evidence.mjs";

const root = process.cwd();
const read = (path) => JSON.parse(readFileSync(path, "utf8"));
const write = (path, value) => writeFileSync(path, JSON.stringify(value, null, 2) + "\n");
const hash = (bytes) => createHash("sha256").update(bytes).digest("hex");
const catalogue = () => read("catalogue/results.json");
const binding = () => read("core/algebraic-kernel-pins.json");
const absent = resolve(".work/no-algebraic-kernel-acceptance");
function evidence(t) {
  const directory = mkdtempSync(join(tmpdir(), "qrh-algebraic-evidence-"));
  t.after(() => rmSync(directory, { recursive: true, force: true }));
  cpSync(KERNEL_DIRECTORY, directory, { recursive: true });
  return directory;
}
function change(directory, path, mutate) {
  const file = join(directory, path), value = read(file);
  mutate(value);
  write(file, value);
  const collection = read(join(directory, "collection.json"));
  collection.files[path] = hash(readFileSync(file));
  write(join(directory, "collection.json"), collection);
}
const validate = (directory, data = catalogue(), pins = binding()) =>
  validateAlgebraicKernelEvidence(root, data, directory, pins);

// Deliberately repin malformed fixtures only when testing the semantic checks
// after the trust anchor. Tampering tests retain the real maintainer pin.
const reviewedFixtureBinding = (directory) => ({
  ...binding(),
  evidence_collection_sha256: hash(readFileSync(join(directory, "collection.json"))),
});

test("algebraic native evidence cannot acquire independent status or a timestamp", () => {
  const data = catalogue(), record = findProofRevision(data, NATIVE_ID);
  record.status = "verification-pending";
  record.first_verified_at = "";
  assert.equal(validate(absent, data), null);
  record.status = "framework-verified";
  assert.throws(() => validate(absent, data), /cannot claim/);
  record.status = "verification-pending";
  record.first_verified_at = "2026-10-09T00:00:00Z";
  assert.throws(() => validate(absent, data), /cannot claim/);
});

test("genuine algebraic acceptance binds all seven targets and its actual source and time", () => {
  const data = catalogue(), report = validate(undefined, data);
  assert.equal(report.status, "PASS");
  assert.equal(report.declarations.length, 7);
  assert.ok(report.declarations.includes("QRHPalomar.existsUniqueRoot"));
  const record = findProofRevision(data, NATIVE_ID);
  record.first_verified_at = "2026-10-09T00:00:00Z";
  assert.throws(() => validate(undefined, data), /date\/source/);
  record.first_verified_at = report.verified_at_utc;
  record.source_commit = "0".repeat(40);
  assert.throws(() => validate(undefined, data), /date\/source/);
});

test("even a reviewed collection must include successful kernel acceptance", (t) => {
  const directory = evidence(t);
  change(directory, "result.json", (report) => { report.judge_exit_code = 1; });
  assert.throws(() => validate(directory, catalogue(), reviewedFixtureBinding(directory)), /acceptance is missing/);
});

test("even a reviewed collection must include root nonvacuity in its scope", (t) => {
  const directory = evidence(t);
  change(directory, "result.json", (report) => { report.declarations.pop(); });
  assert.throws(() => validate(directory, catalogue(), reviewedFixtureBinding(directory)), /target\/kernel\/axiom scope/);
});

test("omitted exports retain their independently recorded sizes and digests", (t) => {
  const directory = evidence(t);
  change(directory, "result.json", (report) => { report.export_sizes["exports/solution.export"]++; });
  assert.throws(() => validate(directory, catalogue(), reviewedFixtureBinding(directory)), /Both independently exported/);
});

test("sanitized receipts cannot replace original checker artifact digests", (t) => {
  const directory = evidence(t);
  change(directory, "publication-transformations.json", (receipt) => {
    receipt.files.find((item) => item.published_path === "judge.log").original_sha256 = "0".repeat(64);
  });
  assert.throws(() => validate(directory, catalogue(), reviewedFixtureBinding(directory)), /Original checker artifact is not linked/);
});

test("the wrapper digest authenticates its complete file map", () => {
  const pins = binding();
  pins.wrappers["Solution.lean"] = "0".repeat(64);
  assert.throws(() => validate(undefined, catalogue(), pins), /wrapper manifest digest/);
});

test("algebraic checks cannot reuse the earlier N24 acceptance dossier", () => {
  assert.throws(() => validate(resolve("public/proofs/nielstron-20261009-kernels")), /Invalid independent evidence collection/);
});

test("a revision cannot bypass its validator through missing, unknown, or ambiguous metadata", () => {
  for (const revision of [undefined, "nielstron-20261009-tightening", "unreviewed-proof"]) {
    const data = catalogue();
    const current = findProofRevision(data, NATIVE_ID);
    if (revision === undefined) delete current.proof_revision;
    else current.proof_revision = revision;
    assert.throws(() => validate(undefined, data), /revision/i);
  }
  const duplicate = catalogue();
  duplicate.records.push(structuredClone(findProofRevision(duplicate, NATIVE_ID)));
  assert.throws(() => validate(undefined, duplicate), /Duplicate catalogue proof revision/);
  const invalidDate = catalogue();
  invalidDate.historical_records[0].timeline_at = "invalid";
  assert.throws(() => validate(undefined, invalidDate), /Invalid catalogue revision timestamp/);
  const historical = catalogue();
  const latest = findProofRevision(historical, NATIVE_ID);
  const previous = historical.historical_records[0];
  historical.records[historical.records.indexOf(latest)] = previous;
  historical.historical_records = [latest];
  assert.throws(() => validate(undefined, historical), /Historical revision/);
});

test("the latest entry must match the algebraic boundary even when N24 history is authentic", () => {
  const data = catalogue();
  findProofRevision(data, NATIVE_ID).theta = data.historical_records[0].theta;
  assert.throws(() => validate(undefined, data), /boundary differs/);
});

test("a consistently rewritten receipt cannot change the reviewed verification time", (t) => {
  const directory = evidence(t);
  const data = catalogue(), pins = binding();
  validate(directory, data, pins);
  const fabricated = "2026-10-10T00:00:00Z";
  for (const name of ["result.json", "original-report.json"]) {
    change(directory, name, (report) => {
      report.verified_at_utc = fabricated;
      report.finished_utc = fabricated;
    });
  }
  const originalHash = hash(readFileSync(join(directory, "original-report.json")));
  change(directory, "publication-transformations.json", (transformations) => {
    const relation = transformations.files.find((item) => item.published_path === "original-report.json");
    relation.original_sha256 = originalHash;
    relation.published_sha256 = originalHash;
  });
  change(directory, "result.json", (report) => {
    report.artifacts["original-report.json"] = originalHash;
  });
  const record = findProofRevision(data, NATIVE_ID);
  record.first_verified_at = fabricated;
  record.timeline_at = fabricated;
  // Reports, transformations, catalogue and every submitted checksum agree.
  // Only the maintainer's independently reviewed pin stays unchanged.
  const collection = read(join(directory, "collection.json"));
  for (const [path, digest] of Object.entries(collection.files)) {
    assert.equal(hash(readFileSync(join(directory, path))), digest);
  }
  assert.throws(() => validate(directory, data, pins), /reviewed evidence collection/);
});

test("acceptance requires a valid independently reviewed collection pin", () => {
  for (const pin of [undefined, null, "invalid", "0".repeat(64)]) {
    const pins = binding();
    pins.evidence_collection_sha256 = pin;
    assert.throws(() => validate(undefined, catalogue(), pins),
      /Invalid frozen algebraic source\/checker binding|reviewed evidence collection/);
  }
});

test("the pinned collection still authenticates its file contents and complete inventory", (t) => {
  const changed = evidence(t);
  writeFileSync(join(changed, "judge.log"), readFileSync(join(changed, "judge.log"), "utf8") + "\nEdited log\n");
  assert.throws(() => validate(changed), /checksum mismatch/);
  const added = evidence(t);
  write(join(added, "unreviewed-report.json"), { status: "PASS" });
  assert.throws(() => validate(added), /inventory differs/);
});
