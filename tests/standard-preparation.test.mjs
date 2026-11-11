import test from "node:test";
import assert from "node:assert/strict";
import {
  mkdtempSync,
  mkdirSync,
  writeFileSync,
  readFileSync,
  rmSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { execFileSync } from "node:child_process";
import { standardChallenge } from "../core/standard-challenge.mjs";
import { fraction } from "../core/rational.mjs";
import { challenge } from "../verifier/challenge.mjs";
const template = { id: "openai-baseline" };
test("dependency-free gate and submission verifier generate the same canonical challenge", () => {
  for (const theta of [
    { numerator: "7", denominator: "8" },
    { numerator: "29", denominator: "33" },
    { numerator: "1", denominator: "1" },
  ]) {
    const text = standardChallenge(fraction(theta));
    assert.equal(text, challenge({ ...template, theta }));
    assert.match(text, /\{q : ℕ\} \[NeZero q\]/);
    assert.match(text, /¬ \(χ = 1 ∧ s = 1\)/);
  }
});

test("date-first directory migration preserves original source binding and rejects changed metadata", (t) => {
  const dir = mkdtempSync(join(tmpdir(), "qrh-standard-dated-"));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const repo = join(dir, "repo");
  mkdirSync(repo);
  const git = (...args) =>
    execFileSync("git", ["-C", repo, ...args], {
      encoding: "utf8",
      stdio: "pipe",
    }).trim();
  git("init", "-q");
  git("config", "user.name", "Fixture");
  git("config", "user.email", "fixture@example.test");
  const originalDirectory = "submissions/fixture-proof";
  const datedDirectory = "submissions/2026-10-12-fixture-proof";
  mkdirSync(join(repo, originalDirectory, "src/Candidate"), {
    recursive: true,
  });
  writeFileSync(
    join(repo, originalDirectory, "src/Candidate/Main.lean"),
    "import Mathlib\n",
  );
  writeFileSync(join(repo, originalDirectory, "metadata.json"), "{}\n");
  git("add", ".");
  git("commit", "-qm", "Original submission");
  const originalHead = git("rev-parse", "HEAD");
  const originalTree = git("rev-parse", `HEAD:${originalDirectory}`);
  git("mv", originalDirectory, datedDirectory);
  git("commit", "-qm", "Date-first folder");
  const datedHead = git("rev-parse", "HEAD");
  const libraries = join(dir, "libraries.json");
  writeFileSync(libraries, "{}\n");
  const run = (head, output) =>
    execFileSync(
      process.execPath,
      [
        resolve("verifier/standard/prepare.mjs"),
        "--checkout",
        repo,
        "--head",
        head,
        "--source-commit",
        originalHead,
        "--repository",
        "fixture/repo",
        "--id",
        "fixture-proof",
        "--bound",
        "7/8",
        "--libraries",
        libraries,
        "--out",
        output,
      ],
      { encoding: "utf8", stdio: "pipe" },
    );
  const output = join(dir, "prepared");
  run(datedHead, output);
  const contract = JSON.parse(
    readFileSync(join(output, "contract.json"), "utf8"),
  );
  assert.equal(contract.manifest.id, "fixture-proof");
  assert.equal(contract.head_sha, datedHead);
  assert.equal(contract.source_commit, originalHead);
  assert.deepEqual(contract.submission_trees, {
    "fixture-proof": originalTree,
  });
  writeFileSync(
    join(repo, datedDirectory, "metadata.json"),
    '{"title":"Changed"}\n',
  );
  git("add", ".");
  git("commit", "-qm", "Changed metadata");
  assert.throws(
    () => run(git("rev-parse", "HEAD"), join(dir, "rejected")),
    /Original dependency source differs from the reviewed head/,
  );
});
test("standard preparation reads the committed source and rejects symlink blobs", () => {
  const dir = mkdtempSync(join(tmpdir(), "qrh-standard-prepare-"));
  try {
    const repo = join(dir, "repo");
    mkdirSync(repo);
    const git = (...args) =>
      execFileSync("git", ["-C", repo, ...args], { encoding: "utf8" }).trim();
    git("init", "-q");
    git("config", "user.name", "Fixture");
    git("config", "user.email", "fixture@example.test");
    mkdirSync(join(repo, "submissions/openai-baseline/src/Candidate"), {
      recursive: true,
    });
    writeFileSync(
      join(repo, "submissions/openai-baseline/src/Candidate/Main.lean"),
      "import Mathlib\n",
    );
    writeFileSync(
      join(repo, "submissions/openai-baseline/metadata.json"),
      "{}",
    );
    git("add", ".");
    git("commit", "-qm", "Fixture");
    const head = git("rev-parse", "HEAD");
    const file = join(
      repo,
      "submissions/openai-baseline/src/Candidate/Main.lean",
    );
    const original = readFileSync(file, "utf8");
    writeFileSync(file, "uncommitted content");
    const libraries = join(dir, "libraries.json");
    writeFileSync(libraries, "{}\n");
    const run = (revision, out) =>
      execFileSync(
        process.execPath,
        [
          resolve("verifier/standard/prepare.mjs"),
          "--checkout",
          repo,
          "--head",
          revision,
          "--repository",
          "fixture/repo",
          "--id",
          "openai-baseline",
          "--bound",
          "7/8",
          "--libraries",
          libraries,
          "--out",
          out,
        ],
        { encoding: "utf8", stdio: "pipe" },
      );
    const out = join(dir, "prepared");
    run(head, out);
    assert.equal(
      readFileSync(join(out, "submission/src/Candidate/Main.lean"), "utf8"),
      original,
    );
    assert.equal(
      JSON.parse(readFileSync(join(out, "contract.json"), "utf8")).head_sha,
      head,
    );
    git(
      "update-index",
      "--add",
      "--cacheinfo",
      `120000,${git("hash-object", "-w", file)},submissions/openai-baseline/src/Candidate/Main.lean`,
    );
    git("commit", "-qm", "Symlink fixture");
    assert.throws(
      () => run(git("rev-parse", "HEAD"), join(dir, "rejected")),
      /Submission requires regular Git files/,
    );
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
