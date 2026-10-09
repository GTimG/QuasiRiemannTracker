import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import {
  validateNativeKernelEvidence,
  NATIVE_ID,
} from "../core/native-kernel-evidence.mjs";

const catalogue = () =>
  JSON.parse(readFileSync("catalogue/results.json", "utf8"));
const absent = resolve(".work/no-such-independent-acceptance-dossier");
test("native evidence alone cannot upgrade the catalogue verification label", () => {
  const data = catalogue(),
    record = data.records.find((r) => r.id === NATIVE_ID);
  record.status = "verification-pending";
  record.first_verified_at = "";
  assert.equal(validateNativeKernelEvidence(process.cwd(), data, absent), null);
  record.status = "framework-verified";
  assert.throws(
    () => validateNativeKernelEvidence(process.cwd(), data, absent),
    /cannot claim/,
  );
});
test("native evidence alone cannot acquire an independent verification timestamp", () => {
  const data = catalogue(),
    record = data.records.find((r) => r.id === NATIVE_ID);
  record.status = "verification-pending";
  record.first_verified_at = "2026-10-09T17:21:30Z";
  assert.throws(
    () => validateNativeKernelEvidence(process.cwd(), data, absent),
    /cannot claim/,
  );
});

test("accepted kernel evidence binds the exact source revision and actual completion time", () => {
  const data = catalogue();
  const report = validateNativeKernelEvidence(process.cwd(), data);
  assert.equal(report.status, "PASS");
  const record = data.records.find((r) => r.id === NATIVE_ID);
  record.first_verified_at = "2026-10-09T17:21:30Z";
  assert.throws(() => validateNativeKernelEvidence(process.cwd(), data), /date\/source/);
  record.first_verified_at = report.verified_at_utc;
  record.source_commit = "0".repeat(40);
  assert.throws(() => validateNativeKernelEvidence(process.cwd(), data), /date\/source/);
});
