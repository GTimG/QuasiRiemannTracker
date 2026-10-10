import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import {
  cpSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";

const ID = "akashlevy-20261009-weighted-numerator";
const SCRIPT = "scripts/check-akashlevy-publication.py";
const sha = (data) => createHash("sha256").update(data).digest("hex");
const TOOL_SHA256 = JSON.parse(
  readFileSync(`proofs/${ID}/evidence/kernels/result.json`, "utf8"),
).tool_sha256;
const run = (...args) =>
  spawnSync("python3", [SCRIPT, ...args], {
    encoding: "utf8",
    env: { ...process.env, PYTHONDONTWRITEBYTECODE: "1" },
  });

// A private copy holding only what the validator reads; the repository is never modified.
function copy() {
  const root = mkdtempSync(join(tmpdir(), "akashlevy-publication-"));
  for (const path of [
    `proofs/${ID}`,
    `proofs/${ID}.sha256.json`,
    `public/proofs/${ID}`,
    "catalogue/results.json",
    "public/proofs/palomar-20261009/qrh/src/Challenge.lean",
    "verifier/akashlevy",
    "public/proofs/akashlevy-20261010-safe-replay",
  ]) {
    if (!existsSync(path)) continue;
    mkdirSync(dirname(join(root, path)), { recursive: true });
    cpSync(path, join(root, path), { recursive: true });
  }
  return root;
}
function rejects(root, pattern, ...args) {
  const result = run("--root", root, ...args);
  assert.notEqual(result.status, 0, "tampered package was accepted");
  assert.match(result.stderr, pattern);
}
// Change a snapshot file, keep its recorded transformation consistent and
// regenerate every derived file, so only the semantic check can object.
function mutateSnapshot(root, path, change) {
  const file = join(root, "proofs", ID, path);
  writeFileSync(file, change(readFileSync(file, "utf8")));
  const record = join(root, "proofs", ID, "publication-transformations.json");
  const transformations = JSON.parse(readFileSync(record, "utf8"));
  for (const item of transformations.changes)
    if (item.path === path) item.published_sha256 = sha(readFileSync(file));
  writeFileSync(record, JSON.stringify(transformations, null, 2) + "\n");
  const result = run("--root", root, "--regenerate");
  assert.equal(result.status, 0, result.stderr || result.stdout);
}
function mutateRecord(root, change) {
  const path = join(root, "catalogue/results.json");
  const data = JSON.parse(readFileSync(path, "utf8"));
  change(data.records.find((r) => r.id === ID));
  writeFileSync(path, JSON.stringify(data, null, 2) + "\n");
}

test("the historical weighted-numerator package and independent verification status are checked", () => {
  const result = run();
  assert.equal(result.status, 0, result.stderr || result.stdout);
  assert.match(
    result.stdout,
    /catalogue verification status validated separately/,
  );
});

test("tampered weighted-numerator evidence and overstated catalogue claims are rejected", () => {
  const cases = [
    [
      (root) => {
        const file = join(
          root,
          "proofs",
          ID,
          "formalization/WeightedQRH/Final.lean",
        );
        writeFileSync(file, readFileSync(file, "utf8") + "\n");
      },
      /Snapshot checksum mismatch/,
    ],
    [
      (root) =>
        mutateSnapshot(
          root,
          "formalization/WeightedQRH/Statements.lean",
          (text) =>
            text.replace(
              "  WeightedQRH.dirichlet_nonzero χ s hs hpole",
              "  True.intro",
            ),
        ),
      /checked source changed.*re-verification required/,
    ],
    [
      (root) => writeFileSync(join(root, "proofs", ID, "unreviewed.txt"), "x"),
      /reviewed publication allowlist/,
    ],
    [
      (root) => {
        const file = join(root, "proofs", ID, "evidence/kernels/judge.log");
        writeFileSync(
          file,
          readFileSync(file, "utf8") + "/" + "Users/someone/work/\n",
        );
      },
      /personal workspace/,
    ],
    [
      (root) =>
        writeFileSync(join(root, "public/proofs", ID, "extra.json"), "{}"),
      /inventory differs/,
    ],
    [
      (root) =>
        mutateSnapshot(root, "evidence/kernels/result.json", (text) =>
          text.replace('"status": "PASS"', '"status": "FAIL"'),
        ),
      /not a PASS/,
    ],
    [
      (root) =>
        mutateSnapshot(root, "evidence/kernels/judge.log", (text) =>
          text.replace("nanoda kernel accepts", "nanoda kernel rejected"),
        ),
      /Kernel artifact differs|three acceptances/,
    ],
    [
      (root) =>
        mutateSnapshot(root, "evidence/kernels/src/Challenge.lean", (text) =>
          text.replace(
            "(10499 / 12000 : ℝ) < s.re) : riemannZeta",
            "(1 / 2 : ℝ) < s.re) : riemannZeta",
          ),
        ),
      /Kernel artifact differs|fixed template/,
    ],
    [
      (root) =>
        mutateSnapshot(
          root,
          "evidence/kernels/controls/ill-typed.log",
          (text) =>
            text.replace(
              "Lean default kernel rejected",
              "Lean default kernel accepted",
            ),
        ),
      /Kernel artifact differs|Ill-typed control/,
    ],
    [
      (root) =>
        mutateRecord(
          root,
          (r) => (r.theta = { numerator: "5249", denominator: "6000" }),
        ),
      /boundary differs/,
    ],
    [
      (root) =>
        mutateRecord(
          root,
          (r) => (r.first_verified_at = "2026-10-10T02:00:00+00:00"),
        ),
      /timeline must use/,
    ],
    [
      (root) => mutateRecord(root, (r) => (r.status = "verification-pending")),
      /Pending record cannot carry/,
    ],
    [
      (root) => mutateRecord(root, (r) => (r.source_commit = "0".repeat(40))),
      /source revision differs/,
    ],
    [
      (root) =>
        mutateRecord(
          root,
          (r) =>
            (r.entrypoint = {
              module: "Solution",
              declaration: "QRHPalomar.allDirichlet",
            }),
        ),
      /all-Dirichlet theorem restated/,
    ],
    [
      (root) => {
        const pin = (text) => text.replaceAll(TOOL_SHA256.lean, "0".repeat(64));
        mutateSnapshot(root, "evidence/kernels/result.json", pin);
        mutateSnapshot(root, "evidence/kernels/tool-pins.json", pin);
      },
      /pinned darwin_aarch64 tools/,
    ],
    [
      (root) =>
        mutateSnapshot(
          root,
          "evidence/comparator/WeightedQRHNegControl.lean",
          (text) => text.replace("(1 / 2 : ℝ)", "(3 / 4 : ℝ)"),
        ),
      /zeta challenge at 1\/2/,
    ],
    // Private metadata outside the shared publication patterns, in a snapshot text file.
    ...[
      ["/priv" + "ate/tmp/claude-run/x", /local temporary path/],
      ["/var/fol" + "ders/xy/T/x", /local temporary path/],
      ["claude" + "-501", /agent scratch path/],
      ["scratch" + "pad/notes", /agent scratch path/],
      ["123e4567-e89b-12d3-a456-" + "426614174000", /bare UUID/],
      ["someone" + "@" + "example.org", /e-mail address/],
    ].map(([value, pattern]) => [
      (root) => {
        const file = join(root, "proofs", ID, "evidence/source-scan.txt");
        writeFileSync(file, readFileSync(file, "utf8") + value + "\n");
      },
      pattern,
    ]),
    [
      (root) => {
        const file = join(root, "public/proofs", ID, "manuscript.pdf");
        writeFileSync(
          file,
          Buffer.concat([
            readFileSync(file),
            Buffer.from("%/priv" + "ate/var/x\n"),
          ]),
        );
        const result = run("--root", root, "--regenerate");
        assert.equal(result.status, 0, result.stderr || result.stdout);
      },
      /local temporary path/,
    ],
  ];
  for (const [mutate, pattern] of cases) {
    const root = copy();
    try {
      const clean = run("--root", root);
      assert.equal(clean.status, 0, clean.stderr || clean.stdout);
      mutate(root);
      rejects(root, pattern);
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  }
});

test("a pending listing of the same evidence needs an empty verification date", () => {
  const root = copy();
  try {
    mutateRecord(root, (r) => {
      r.status = "verification-pending";
      r.first_verified_at = "";
    });
    const result = run("--root", root);
    assert.equal(result.status, 0, result.stderr || result.stdout);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});
