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

test("algebraic native evidence cannot acquire independent status or a timestamp", () => {
  const data = catalogue(), record = data.records.find((row) => row.id === NATIVE_ID);
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
  const record = data.records.find((row) => row.id === NATIVE_ID);
  record.first_verified_at = "2026-10-09T00:00:00Z";
  assert.throws(() => validate(undefined, data), /date\/source/);
  record.first_verified_at = report.verified_at_utc;
  record.source_commit = "0".repeat(40);
  assert.throws(() => validate(undefined, data), /date\/source/);
});

test("a rehashed collection cannot conceal a failed kernel exit", (t) => {
  const directory = evidence(t);
  change(directory, "result.json", (report) => { report.judge_exit_code = 1; });
  assert.throws(() => validate(directory), /acceptance is missing/);
});

test("a rehashed collection cannot remove root nonvacuity from the scope", (t) => {
  const directory = evidence(t);
  change(directory, "result.json", (report) => { report.declarations.pop(); });
  assert.throws(() => validate(directory), /target\/kernel\/axiom scope/);
});

test("omitted exports retain their independently recorded sizes and digests", (t) => {
  const directory = evidence(t);
  change(directory, "result.json", (report) => { report.export_sizes["exports/solution.export"]++; });
  assert.throws(() => validate(directory), /Both independently exported/);
});

test("sanitized receipts cannot replace original checker artifact digests", (t) => {
  const directory = evidence(t);
  change(directory, "publication-transformations.json", (receipt) => {
    receipt.files.find((item) => item.published_path === "judge.log").original_sha256 = "0".repeat(64);
  });
  assert.throws(() => validate(directory), /Original checker artifact is not linked/);
});

test("the wrapper digest authenticates its complete file map", () => {
  const pins = binding();
  pins.wrappers["Solution.lean"] = "0".repeat(64);
  assert.throws(() => validate(undefined, catalogue(), pins), /wrapper manifest digest/);
});

test("algebraic checks cannot reuse the earlier N24 acceptance dossier", () => {
  assert.throws(() => validate(resolve("public/proofs/nielstron-20261009-kernels")), /Invalid independent evidence collection/);
});
