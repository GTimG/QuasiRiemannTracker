import test from "node:test";
import assert from "node:assert/strict";
import {
  cpSync,
  mkdtempSync,
  mkdirSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { cachePlan } from "../verifier/actions/cache.mjs";

const platform = { os: "Linux", arch: "X64" };

function checkout(t) {
  const root = mkdtempSync(join(tmpdir(), "qrh-cache-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  for (const path of ["verifier", ".github/actions/verifier-cache"])
    cpSync(path, join(root, path), { recursive: true });
  mkdirSync(join(root, "submissions/example/src"), { recursive: true });
  writeFileSync(
    join(root, "submissions/example/src/Main.lean"),
    "import OAI.NumberTheory.DirichletL.Nonvanishing\n",
  );
  return root;
}

test("workers share an environment across PRs, results and workspace paths", (t) => {
  const a = checkout(t),
    b = checkout(t);
  mkdirSync(join(a, "verification"));
  mkdirSync(join(b, "verification"));
  writeFileSync(
    join(a, "verification/imports.json"),
    '["OAI.AdditionalPRImport"]',
  );
  writeFileSync(join(b, "verification/imports.json"), "[]");
  writeFileSync(
    join(a, "verification/attempt.json"),
    '{"result_id":"first","head_sha":"aaaa"}',
  );
  writeFileSync(
    join(b, "verification/attempt.json"),
    '{"result_id":"second","head_sha":"bbbb"}',
  );
  assert.deepEqual(cachePlan(a, platform), cachePlan(b, platform));
  assert.equal(cachePlan(a, platform).path, "verification/environment");
});

test("dependency, toolchain and setup changes invalidate the shared environment", (t) => {
  const root = checkout(t);
  const before = cachePlan(root, platform).key;
  for (const file of [
    "verifier/pins.json",
    "verifier/worker_resources.py",
    "verifier/standard/tool-pins.json",
    "verifier/standard/lake-manifest.json",
    "verifier/standard/lakefile.lean",
    "verifier/actions/setup.py",
    "verifier/actions/library_contract.py",
  ]) {
    const path = join(root, file),
      original = readFileSync(path);
    writeFileSync(path, Buffer.concat([original, Buffer.from("\n")]));
    assert.notEqual(cachePlan(root, platform).key, before, file);
    writeFileSync(path, original);
  }
  assert.throws(
    () => cachePlan(root, { os: "Linux", arch: "ARM64" }),
    /Linux X64/,
  );
  assert.throws(
    () => cachePlan(root, { os: "Windows", arch: "X64" }),
    /Linux X64/,
  );
});

test("submission source changes preserve the shared toolchain and package cache", (t) => {
  const root = checkout(t),
    file = join(root, "submissions/example/src/Main.lean");
  const before = cachePlan(root, platform);
  writeFileSync(
    file,
    `import OAI.NumberTheory.DirichletL.Nonvanishing
import Candidate.Other
/- import OAI.Unused -/
def text := "import OAI.Fake"
theorem example : True := by trivial
`,
  );
  assert.deepEqual(cachePlan(root, platform), before);
  writeFileSync(
    file,
    readFileSync(file, "utf8") + "\nimport OAI.NumberTheory.Additional\n",
  );
  const after = cachePlan(root, platform);
  assert.deepEqual(after, before);
});
