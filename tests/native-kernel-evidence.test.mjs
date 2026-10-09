import test from "node:test";
import assert from "node:assert/strict";
import {
  readFileSync,
  mkdtempSync,
  mkdirSync,
  cpSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { createHash } from "node:crypto";
import { tmpdir } from "node:os";
import { resolve, join, dirname } from "node:path";
import {
  validateNativeKernelEvidence,
  NATIVE_ID,
  KERNEL_DIRECTORY,
  SOURCE_ARCHIVE,
  PUBLISHED_SOURCE_ARCHIVE,
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

test("repackaging preserves the historical receipt and every checked proof source", (t) => {
  const root = mkdtempSync(join(tmpdir(), "qrh-repackaged-evidence-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const archive = `public/proofs/${NATIVE_ID}/source-public.tar.gz`;
  const formalization = `proofs/${NATIVE_ID}/compressed/formalization`;
  for (const path of [
    "public/proofs/palomar-20261009/qrh/src/Challenge.lean",
    `proofs/${NATIVE_ID}/tightening/reproduction.json`,
    formalization,
    archive,
  ]) {
    mkdirSync(dirname(join(root, path)), { recursive: true });
    cpSync(path, join(root, path), { recursive: true });
  }
  const validate = () =>
    validateNativeKernelEvidence(root, catalogue(), resolve(KERNEL_DIRECTORY));
  const report = validate();
  assert.equal(report.source_archive_sha256, SOURCE_ARCHIVE);
  const archiveBytes = readFileSync(join(root, archive));
  assert.equal(
    createHash("sha256").update(archiveBytes).digest("hex"),
    PUBLISHED_SOURCE_ARCHIVE,
  );
  assert.notEqual(PUBLISHED_SOURCE_ARCHIVE, SOURCE_ARCHIVE);

  const replay = JSON.parse(
    readFileSync(
      join(root, `proofs/${NATIVE_ID}/tightening/reproduction.json`),
    ),
  );
  const source = join(
    root,
    formalization,
    Object.keys(replay.files).find((path) => path.endsWith(".lean")),
  );
  const original = readFileSync(source);
  writeFileSync(
    source,
    Buffer.concat([original, Buffer.from("\n-- changed after verification\n")]),
  );
  assert.throws(validate, /Checker source differs from immutable submission/);
  writeFileSync(source, original);
  writeFileSync(
    join(root, archive),
    Buffer.concat([archiveBytes, Buffer.from("changed")]),
  );
  assert.throws(validate, /Reviewed published native source archive changed/);
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
  assert.throws(
    () => validateNativeKernelEvidence(process.cwd(), data),
    /date\/source/,
  );
  record.first_verified_at = report.verified_at_utc;
  record.source_commit = "0".repeat(40);
  assert.throws(
    () => validateNativeKernelEvidence(process.cwd(), data),
    /date\/source/,
  );
});
