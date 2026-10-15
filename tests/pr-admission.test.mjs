import test, { after, mock } from "node:test";
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
mkdirSync(join(root, "verifier"));
writeFileSync(
  join(root, "verifier/pr-admissions.json"),
  JSON.stringify({ schema_version: 1, admissions: [] }),
);
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
    validateMaintenance: mock.fn(() => []),
    validateEvidence: mock.fn(() => {
      throw new Error("Unexpected evidence validation");
    }),
  };
}

// Accept either a synchronous or asynchronous implementation of the gate.
const run = (input) => Promise.resolve().then(() => evaluatePR(input));

async function rejectsBeforeEvidence(input, message) {
  await assert.rejects(run(input), { message });
  assert.equal(input.validateEvidence.mock.callCount(), 0);
}

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

for (const [description, body, message] of [
  [
    "incorrectly cased fields",
    newBound.toLowerCase(),
    "Malformed or unknown QRH declaration field",
  ],
  [
    "the obsolete maintenance type",
    "QRH-Type: maintenance",
    "Malformed or unknown QRH declaration field",
  ],
  [
    "the obsolete new-bound type",
    `QRH-Type: new-bound\n${newBound}`,
    "Malformed or unknown QRH declaration field",
  ],
  [
    "a missing colon",
    "QRH-Result candidate-20261011",
    "Malformed or unknown QRH declaration field",
  ],
  [
    "an unknown field",
    `${maintenance}\nQRH-Override: true`,
    "Malformed or unknown QRH declaration field",
  ],
  [
    "a missing decimal",
    newBound.replace(`\nQRH-Decimal: ${approximation}`, ""),
    "QRH-Decimal must have a canonical integer part and 1–200 fractional digits",
  ],
  [
    "a duplicate decimal",
    `${newBound}\nQRH-Decimal: ${approximation}`,
    "Duplicate QRH declaration field",
  ],
  [
    "an empty decimal",
    newBound.replace(approximation, ""),
    "Malformed or unknown QRH declaration field",
  ],
  [
    "scientific notation",
    newBound.replace(approximation, "8.748866e-1"),
    "QRH-Decimal must have a canonical integer part and 1–200 fractional digits",
  ],
  [
    "a missing result",
    newBound.replace(`QRH-Result: ${resultId}\n`, ""),
    "New bounds require QRH-Result: <stable-result-id>",
  ],
  [
    "a missing bound",
    newBound.replace(`QRH-Bound: ${bound}\n`, ""),
    "New bounds require QRH-Bound: <exact checked value>",
  ],
  [
    "a duplicate result",
    `${newBound}\nQRH-Result: ${resultId}`,
    "Duplicate QRH declaration field",
  ],
  [
    "a duplicate bound",
    `${newBound}\nQRH-Bound: ${bound}`,
    "Duplicate QRH declaration field",
  ],
  [
    "an empty result",
    newBound.replace(resultId, ""),
    "Malformed or unknown QRH declaration field",
  ],
  [
    "an uppercase result",
    newBound.replace(resultId, "Candidate-20261011"),
    "New bounds require QRH-Result: <stable-result-id>",
  ],
  [
    "a short result",
    newBound.replace(resultId, "ab"),
    "New bounds require QRH-Result: <stable-result-id>",
  ],
  [
    "a path as result",
    newBound.replace(resultId, "../candidate"),
    "New bounds require QRH-Result: <stable-result-id>",
  ],
  [
    "an empty bound",
    newBound.replace(bound, ""),
    "Malformed or unknown QRH declaration field",
  ],
  [
    "an oversized bound",
    newBound.replace(bound, "1".repeat(257)),
    "New bounds require QRH-Bound: <exact checked value>",
  ],
]) {
  test(`declaration rejects ${description}`, () => {
    assert.throws(() => parseDeclaration(body), { message });
  });
}

test("rejects result declaration fields mixed with maintenance changes", async () => {
  for (const body of [
    newBound,
    `QRH-Result: ${resultId}`,
    `QRH-Bound: ${bound}`,
    `QRH-Decimal: ${approximation}`,
    "QRH-Result candidate-20261011",
  ]) {
    assert.equal(hasResultSection(body), true, body);
    await rejectsBeforeEvidence(
      options(body),
      "Submit QRH results and maintenance changes in separate PRs",
    );
  }
});

for (const filename of [
  "submissions/candidate-20261011/src/Candidate/Main.lean",
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
        previous_filename:
          "submissions/candidate-20261011/src/Candidate/Main.lean",
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

for (const [description, files] of [
  ["proof source", [file("proofs/solution.lean")]],
  ["catalogue", [file("catalogue/results.json")]],
  [
    "cleanup across code and proof paths",
    [
      file("proofs/old/Main.lean", { status: "removed" }),
      file("src/App.tsx"),
      file("public/catalogue.json"),
    ],
  ],
  [
    "proof-to-maintenance rename",
    [
      file("docs/old-proof.txt", {
        status: "renamed",
        previous_filename: "public/proofs/candidate/report.json",
      }),
    ],
  ],
]) {
  for (const body of [
    "Clean up existing records.",
    "",
    null,
    "## New bound",
    "## QRH result",
  ]) {
    test(`defaults to maintenance for ${description} with body=${JSON.stringify(body)}`, async () => {
      const input = options(body, files);
      assert.deepEqual(classifyPRChanges(input), {
        proof: false,
        maintenance: true,
      });
      assert.match(await run(input), /Maintenance requirements satisfied/);
      assert.equal(input.validateMaintenance.mock.callCount(), 1);
      assert.equal(input.validateEvidence.mock.callCount(), 0);
    });
  }
}

test("a new-bound declaration requires a proof-bearing change", async () => {
  await rejectsBeforeEvidence(
    options(newBound),
    "Submit QRH results and maintenance changes in separate PRs",
  );
});

test("PR #8's result metadata and maintenance changes fail the mixed-change requirement first", async () => {
  const body = [
    "QRH-Result: single-prime-29-33-20261010",
    "QRH-Bound: 29/33",
    "QRH-Decimal: 0.87878787",
  ].join("\n");
  const input = options(body, [
    file("submissions/single-prime-29-33-20261010/src/Candidate/Main.lean"),
    file("tests/browser/dashboard.spec.ts"),
  ]);
  input.pr.number = 8;
  await rejectsBeforeEvidence(
    input,
    "Submit QRH results and maintenance changes in separate PRs",
  );
});

test("PR #8's proof-only 29/33 submission reaches the live verification requirement", async () => {
  const input = options(
    newBound
      .replace(resultId, "single-prime-29-33-20261010")
      .replace(bound, "29/33")
      .replace(approximation, "0.87878787"),
    [file("submissions/single-prime-29-33-20261010/src/Candidate/Main.lean")],
  );
  input.pr.number = 8;
  delete input.validateEvidence;
  await assert.rejects(run(input), {
    message: "Proof verification has not run for this PR head",
  });
});

for (const draft of [false, true]) {
  test(`PR #15's declaration requires live verification as ${draft ? "a draft" : "ready for review"}`, async () => {
    const input = options(
      newBound.replace(resultId, "gao-local-moment-20261011"),
      [file("submissions/gao-local-moment-20261011/src/Candidate/Main.lean")],
    );
    input.pr.draft = draft;
    delete input.validateEvidence;
    await assert.rejects(run(input), {
      message: "Proof verification has not run for this PR head",
    });
  });

  test(`new-bound admission binds evidence to the repository, PR, current head, result and value for draft=${draft}`, async () => {
    const input = options(newBound, [
      file("submissions/candidate-20261011/src/Candidate/Main.lean"),
    ]);
    input.pr.draft = draft;
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
}

for (const [theta, decimal] of [
  ["29/33", "0.87878787"],
  ["7/8", "0.875"],
  ["1/1", "1.0"],
  ["3/2", "1.5"],
  ["683505193/781250000", "0.87488664704"],
]) {
  test(`accepts ${theta} with authenticated evidence and an accurate decimal`, async () => {
    const input = options(
      newBound.replace(bound, theta).replace(approximation, decimal),
      [file("submissions/candidate-20261011/src/Candidate/Main.lean")],
    );
    input.validateEvidence = mock.fn(() => ({ theta_exact: theta }));
    assert.equal(
      await run(input),
      `Proof verification accepts ${resultId} at ${theta} for this exact PR head. Decimal ${decimal} accurately approximates the exact bound.`,
    );
    assert.equal(input.validateEvidence.mock.callCount(), 1);
    assert.deepEqual(input.validateEvidence.mock.calls[0].arguments, [
      root,
      {
        repository,
        number: input.pr.number,
        head_sha: head,
        result_id: resultId,
        theta_exact: theta,
      },
    ]);
  });
}

for (const [theta, message] of [
  ["0/1", "Bound must be positive"],
  ["-1/1", "Bound must be positive"],
  ["2/2", "Rational must be normalized."],
  [
    "01/1",
    "Use canonical integer strings and a positive denominator (maximum 200 digits).",
  ],
  [
    "1/0",
    "Use canonical integer strings and a positive denominator (maximum 200 digits).",
  ],
]) {
  test(`rejects invalid bound ${theta} before evidence validation`, async () => {
    await rejectsBeforeEvidence(
      options(newBound.replace(bound, theta), [
        file("submissions/candidate-20261011/src/Candidate/Main.lean"),
      ]),
      message,
    );
  });
}

test("propagates evidence validation failures to PR admission", async () => {
  const input = options(newBound, [
    file("submissions/candidate-20261011/src/Candidate/Main.lean"),
  ]);
  input.validateEvidence = () => {
    throw new Error("No trusted admission receipt for this PR head");
  };
  await assert.rejects(run(input), {
    message: "No trusted admission receipt for this PR head",
  });
});

test("requires accurate and distinguishing decimal digits with accepted evidence", async () => {
  for (const [decimal, message] of [
    [
      "0.8748866",
      "QRH-Decimal needs more digits to differ from the previous bound (previous-result: 0.8748866)",
    ],
    [
      "0.87488661",
      "QRH-Decimal must give the exact bound's truncated digits: 0.87488660",
    ],
  ]) {
    const input = options(newBound.replace(approximation, decimal), [
      file("submissions/candidate-20261011/src/Candidate/Main.lean"),
    ]);
    input.validateEvidence = mock.fn(() => ({ theta_exact: bound }));
    await assert.rejects(run(input), { message });
    assert.equal(input.validateEvidence.mock.callCount(), 1);
  }
});

test("irrational decimal digits require an enclosure from authenticated evidence", async () => {
  const body = newBound
    .replace(bound, "sqrt(3)/2")
    .replace(approximation, "0.866025");
  const input = options(body, [
    file("submissions/candidate-20261011/src/Candidate/Main.lean"),
  ]);
  input.validateEvidence = mock.fn(() => ({ theta_exact: "sqrt(3)/2" }));
  await assert.rejects(run(input), {
    message:
      "The exact algebraic bound needs a trusted certified bound_interval",
  });
  assert.equal(input.validateEvidence.mock.callCount(), 1);
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
  const input = options(newBound, [
    file("submissions/candidate-20261011/src/Candidate/Main.lean"),
  ]);
  input.pr.head.sha = "b".repeat(40);
  input.validateEvidence = (_root, subject) => {
    assert.equal(subject.head_sha, input.pr.head.sha);
    if (subject.head_sha !== head)
      throw new Error("Receipt head does not match");
  };
  await assert.rejects(run(input), { message: "Receipt head does not match" });
});

for (const filename of [
  ".github/workflows/ci.yml",
  "core/trust-root.json",
  "verifier/pr-admission.mjs",
  "tests/pr-admission.test.mjs",
  "README.md",
]) {
  test(`bound declarations require a separate maintenance PR for ${filename}`, async () => {
    const input = options(newBound, [
      file("submissions/candidate-20261011/src/Candidate/Main.lean"),
      file(filename),
    ]);
    assert.deepEqual(classifyPRChanges(input), {
      proof: true,
      maintenance: true,
    });
    await rejectsBeforeEvidence(
      input,
      "Submit QRH results and maintenance changes in separate PRs",
    );
  });
}

for (const [description, mutate, message] of [
  [
    "closed PR",
    (input) => (input.pr.state = "closed"),
    "Admission requires an open PR",
  ],
  [
    "different base branch",
    (input) => (input.pr.base.ref = "other"),
    "Admission requires a PR targeting this repository's default branch",
  ],
  [
    "different base repository",
    (input) => (input.pr.base.repo.full_name = "Elsewhere/Tracker"),
    "Admission requires a PR targeting this repository's default branch",
  ],
  [
    "missing head",
    (input) => delete input.pr.head,
    "Invalid PR identity or head commit",
  ],
  [
    "short head SHA",
    (input) => (input.pr.head.sha = "abcd"),
    "Invalid PR identity or head commit",
  ],
  [
    "nonhex head SHA",
    (input) => (input.pr.head.sha = "z".repeat(40)),
    "Invalid PR identity or head commit",
  ],
  [
    "truncated file list",
    (input) => (input.pr.changed_files = 2),
    "Incomplete or duplicate PR file list; refusing a truncated diff",
  ],
  [
    "inconsistent file count",
    (input) => (input.pr.changed_files = 0),
    "Incomplete or duplicate PR file list; refusing a truncated diff",
  ],
]) {
  test(`admission rejects a ${description}`, async () => {
    const input = options();
    mutate(input);
    assert.throws(() => classifyPRChanges(input), { message });
    await rejectsBeforeEvidence(input, message);
  });
}

for (const draft of [false, true]) {
  test(`maintenance checks every affected proof for draft=${draft}`, async () => {
    const input = options("", [
      file("submissions/first/src/Candidate/Main.lean"),
      file("src/App.tsx"),
    ]);
    input.pr.draft = draft;
    input.validateMaintenance = () => [
      { result_id: "first", theta_exact: "1/1" },
      { result_id: "second", theta_exact: "7/8" },
    ];
    input.validateEvidence = mock.fn(() => ({}));
    assert.match(await run(input), /2 proof/);
    assert.deepEqual(
      input.validateEvidence.mock.calls.map((c) => c.arguments[1]),
      [
        {
          repository,
          number: 15,
          head_sha: head,
          result_id: "first",
          theta_exact: "1/1",
        },
        {
          repository,
          number: 15,
          head_sha: head,
          result_id: "second",
          theta_exact: "7/8",
        },
      ],
    );
    input.validateEvidence = () => {
      throw Error("Forbidden axiom: sorryAx");
    };
    await assert.rejects(run(input), /Forbidden axiom: sorryAx/);
  });
}
test("maintenance propagates invalid bound metadata before proof checking", async () => {
  const input = options("", [
    file("catalogue/results.json"),
    file("src/App.tsx"),
  ]);
  input.validateMaintenance = () => {
    throw Error("Verification record differs from catalogue: first");
  };
  await rejectsBeforeEvidence(
    input,
    "Verification record differs from catalogue: first",
  );
});

for (const change of [
  file("submissions/openai-baseline/src/Submissions/openai_baseline/Main.lean"),
  file(`submissions/${resultId}/src/Candidate/Main.lean`, {
    status: "renamed",
    previous_filename: "submissions/another-proof/src/Candidate/Main.lean",
  }),
])
  test(`new result declarations cannot conceal maintenance of ${change.previous_filename ?? change.filename}`, async () => {
    const input = options(newBound, [change]);
    await assert.rejects(
      run(input),
      /edit existing submissions in a maintenance PR/,
    );
    assert.equal(input.validateEvidence.mock.callCount(), 0);
  });
