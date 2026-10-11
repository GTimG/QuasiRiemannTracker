import test, { after } from "node:test";
import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  classifyChanges,
  classifyPRChanges,
  evaluatePR,
  hasResultSection,
  parseDeclaration,
} from "../verifier/pr-admission.mjs";

const repository = "GTimG/QuasiRiemannTracker";
const defaultBranch = "main";
const head = "a".repeat(40);
const root = mkdtempSync(join(tmpdir(), "qrh-admission-tests-"));
after(() => rmSync(root, { recursive: true, force: true }));
mkdirSync(join(root, "catalogue"));
writeFileSync(
  join(root, "catalogue/results.json"),
  JSON.stringify({
    records: [
      {
        id: "previous-result",
        status: "framework-verified",
        theta: { numerator: "683505193", denominator: "781250000" },
      },
    ],
  }),
);
const bound = "4374433/5000000";
const approximation = "0.87488660";
const resultId = "candidate-20261011";
const maintenance = "Updates the tracker documentation.";
const newBound = [
  `QRH-Result: ${resultId}`,
  `QRH-Bound: ${bound}`,
  `QRH-Decimal: ${approximation}`,
].join("\n");
const file = (filename, extra = {}) => ({
  filename,
  status: "added",
  ...extra,
});

function options(body = maintenance, files = [file("README.md")]) {
  return {
    repository,
    defaultBranch,
    root,
    files,
    pr: {
      number: 15,
      state: "open",
      draft: false,
      body,
      changed_files: files.length,
      base: { ref: defaultBranch, repo: { full_name: repository } },
      head: { sha: head },
    },
    validateEvidence: () => {
      throw new Error("Unexpected evidence validation");
    },
  };
}

// Accept either a synchronous or asynchronous implementation of the gate.
const run = (input) => Promise.resolve().then(() => evaluatePR(input));

test("accepts plain maintenance prose", () => {
  for (const body of [maintenance, "", null, "An inline QRH-Result: example"]) {
    assert.equal(parseDeclaration(body), null);
    assert.equal(hasResultSection(body), false);
  }
});

test("a new-bound declaration preserves the exact claimed value", () => {
  assert.deepEqual(parseDeclaration(`A proposed bound.\n\n${newBound}\n`), {
    result_id: resultId,
    theta_exact: bound,
    theta_decimal: approximation,
  });
});

for (const [description, body] of [
  ["the obsolete maintenance type", "QRH-Type: maintenance"],
  ["the obsolete new-bound type", `QRH-Type: new-bound\n${newBound}`],
  ["a missing colon", "QRH-Result candidate-20261011"],
  ["an unknown field", `${maintenance}\nQRH-Override: true`],
  [
    "a missing decimal",
    newBound.replace(`\nQRH-Decimal: ${approximation}`, ""),
  ],
  ["a duplicate decimal", `${newBound}\nQRH-Decimal: ${approximation}`],
  ["an empty decimal", newBound.replace(approximation, "")],
  ["scientific notation", newBound.replace(approximation, "8.748866e-1")],
  ["a missing result", newBound.replace(`QRH-Result: ${resultId}\n`, "")],
  ["a missing bound", newBound.replace(`QRH-Bound: ${bound}\n`, "")],
  ["a duplicate result", `${newBound}\nQRH-Result: ${resultId}`],
  ["a duplicate bound", `${newBound}\nQRH-Bound: ${bound}`],
  ["an empty result", newBound.replace(resultId, "")],
  ["an uppercase result", newBound.replace(resultId, "Candidate-20261011")],
  ["a short result", newBound.replace(resultId, "ab")],
  ["a path as result", newBound.replace(resultId, "../candidate")],
  ["an empty bound", newBound.replace(bound, "")],
  ["an oversized bound", newBound.replace(bound, "1".repeat(257))],
]) {
  test(`declaration rejects ${description}`, () => {
    assert.throws(() => parseDeclaration(body));
  });
}

test("rejects result metadata and headings in maintenance PRs", async () => {
  for (const body of [
    newBound,
    `QRH-Result: ${resultId}`,
    `QRH-Bound: ${bound}`,
    `QRH-Decimal: ${approximation}`,
    "QRH-Result candidate-20261011",
    "## New bound\nA proposed improvement.",
    "## QRH result\nA proposed improvement.",
    "## nEw BoUnD\nA proposed improvement.",
  ]) {
    assert.equal(hasResultSection(body), true, body);
    await assert.rejects(run(options(body)), undefined, body);
  }
});

for (const filename of [
  "proofs/candidate/Main.lean",
  "public/proofs/candidate/report.json",
  "submissions/candidate.json",
  "catalogue/records/candidate.json",
  "registry/records/candidate.json",
  "public/catalogue.json",
  "public/registry.json",
  "Candidate/Main.lean",
  "Main.lean",
]) {
  test(`classifies ${filename} as proof-bearing`, () => {
    assert.deepEqual(classifyChanges([file(filename)]), {
      proof: true,
      maintenance: false,
    });
  });
}

test("classifies maintenance paths and trusted Lean fixtures as maintenance", () => {
  assert.deepEqual(
    classifyChanges([
      file("README.md"),
      file("src/App.tsx"),
      file("docs/submission.md"),
      file(".github/workflows/ci.yml"),
      file("core/Challenge.lean"),
      file("verifier/fixtures/Example.lean"),
      file("tests/fixtures/Example.lean"),
    ]),
    { proof: false, maintenance: true },
  );
});

test("renaming a proof to a maintenance path classifies both sides of the rename", () => {
  assert.deepEqual(
    classifyChanges([
      file("docs/old-proof.txt", {
        status: "renamed",
        previous_filename: "proofs/candidate/Main.lean",
      }),
    ]),
    { proof: true, maintenance: true },
  );
});

test("accepts a maintenance PR with plain prose", async () => {
  const summary = await run(options());
  assert.equal(typeof summary, "string");
  assert.ok(summary.length > 0);
});

test("requires a result declaration for PR #15's proof change", async () => {
  const input = options("Adds the Lean proof.", [file("proofs/solution.lean")]);
  input.pr.number = 15;
  await assert.rejects(run(input));
});

test("requires result metadata for proof submissions", async () => {
  await assert.rejects(
    run(options(maintenance, [file("proofs/candidate/Main.lean")])),
  );
});

test("rejects proof-to-maintenance renames", async () => {
  await assert.rejects(
    run(
      options(maintenance, [
        file("docs/old-proof.txt", {
          status: "renamed",
          previous_filename: "public/proofs/candidate/report.json",
        }),
      ]),
    ),
  );
});

test("a new-bound declaration requires a proof-bearing change", async () => {
  await assert.rejects(run(options(newBound)));
});

test("new-bound admission binds evidence to the repository, PR, current head, result and value", async () => {
  const input = options(newBound, [file("proofs/candidate/Main.lean")]);
  const calls = [];
  input.validateEvidence = (...args) => {
    calls.push(args);
    return { result_id: resultId, theta_exact: bound };
  };
  const summary = await run(input);
  assert.equal(typeof summary, "string");
  assert.ok(summary.length > 0);
  assert.deepEqual(calls, [
    [
      root,
      {
        repository,
        number: 15,
        head_sha: head,
        result_id: resultId,
        theta_exact: bound,
      },
    ],
  ]);
});

test("propagates evidence validation failures to PR admission", async () => {
  const input = options(newBound, [file("proofs/candidate/Main.lean")]);
  input.validateEvidence = () => {
    throw new Error("No trusted admission receipt for this PR head");
  };
  await assert.rejects(run(input), /No trusted admission receipt/);
});

test("requires accurate and distinguishing decimal digits with accepted evidence", async () => {
  for (const decimal of ["0.8748866", "0.87488661"]) {
    const input = options(newBound.replace(approximation, decimal), [
      file("proofs/candidate/Main.lean"),
    ]);
    input.validateEvidence = () => ({ theta_exact: bound });
    await assert.rejects(run(input));
  }
});

test("irrational decimal digits require an enclosure from authenticated evidence", async () => {
  const body = newBound
    .replace(bound, "sqrt(3)/2")
    .replace(approximation, "0.866025");
  const input = options(body, [file("proofs/candidate/Main.lean")]);
  input.validateEvidence = () => ({ theta_exact: "sqrt(3)/2" });
  await assert.rejects(run(input));
  input.validateEvidence = () => ({
    theta_exact: "sqrt(3)/2",
    bound_interval: {
      lower: { numerator: "4330127", denominator: "5000000" },
      upper: { numerator: "17320509", denominator: "20000000" },
    },
  });
  assert.match(await run(input), /0\.866025/);
});

test("requires a matching receipt after the PR head changes", async () => {
  const input = options(newBound, [file("proofs/candidate/Main.lean")]);
  input.pr.head.sha = "b".repeat(40);
  input.validateEvidence = (_root, subject) => {
    assert.equal(subject.head_sha, input.pr.head.sha);
    if (subject.head_sha !== head)
      throw new Error("Receipt head does not match");
  };
  await assert.rejects(run(input), /Receipt head does not match/);
});

for (const filename of [
  ".github/workflows/ci.yml",
  "core/trust-root.json",
  "verifier/pr-admission.mjs",
  "tests/pr-admission.test.mjs",
  "README.md",
]) {
  test(`requires a separate maintenance PR for ${filename}`, async () => {
    let evidenceCalls = 0;
    for (const body of [maintenance, newBound]) {
      const input = options(body, [
        file("proofs/candidate/Main.lean"),
        file(filename),
      ]);
      assert.deepEqual(classifyPRChanges(input), {
        proof: true,
        maintenance: true,
      });
      input.validateEvidence = () => {
        evidenceCalls++;
      };
      await assert.rejects(run(input));
    }
    assert.equal(evidenceCalls, 0);
  });
}

for (const [description, mutate] of [
  ["closed PR", (input) => (input.pr.state = "closed")],
  ["different base branch", (input) => (input.pr.base.ref = "other")],
  [
    "different base repository",
    (input) => (input.pr.base.repo.full_name = "Elsewhere/Tracker"),
  ],
  ["missing head", (input) => delete input.pr.head],
  ["short head SHA", (input) => (input.pr.head.sha = "abcd")],
  ["nonhex head SHA", (input) => (input.pr.head.sha = "z".repeat(40))],
  ["truncated file list", (input) => (input.pr.changed_files = 2)],
  ["inconsistent file count", (input) => (input.pr.changed_files = 0)],
]) {
  test(`admission rejects a ${description}`, async () => {
    const input = options();
    mutate(input);
    assert.throws(() => classifyPRChanges(input));
    await assert.rejects(run(input));
  });
}
