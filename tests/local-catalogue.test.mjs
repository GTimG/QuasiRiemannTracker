import test from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";
import {
  buildSubmissionCatalogue,
  readSubmissions,
  submissionBound,
} from "../scripts/submission-catalogue.mjs";

const repository = "owner/repository";
const metadata = {
  title: "An exact improvement",
  authors: [{ name: "Original Author" }],
  description: "The contributor's argument, with the original attribution.",
  license: "Apache-2.0",
  references: [{ label: "Original source", url: "https://example.com/proof" }],
};
const theorem = (bound = "7 / 8") => `
namespace Candidate
theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (${bound} : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  exact existing_proof χ hs hpole
end Candidate
`;

function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), "qrh-local-catalogue-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const git = (...args) =>
    execFileSync("git", args, {
      cwd: root,
      encoding: "utf8",
      stdio: ["ignore", "pipe", "pipe"],
    }).trim();
  const write = (path, value) => {
    const target = join(root, path);
    mkdirSync(join(target, ".."), { recursive: true });
    writeFileSync(
      target,
      typeof value === "string" ? value : JSON.stringify(value, null, 2),
    );
  };
  const submission = (directory, options = {}) => {
    write(
      `submissions/${directory}/metadata.json`,
      options.metadata || metadata,
    );
    write(
      `submissions/${directory}/src/Candidate/Main.lean`,
      options.source || theorem(),
    );
  };
  const commit = (date, message = "Add source") => {
    git("add", ".");
    execFileSync(
      "git",
      [
        "-c",
        "user.name=Test",
        "-c",
        "user.email=test@example.com",
        "commit",
        "-qm",
        message,
      ],
      {
        cwd: root,
        env: {
          ...process.env,
          GIT_AUTHOR_DATE: date,
          GIT_COMMITTER_DATE: date,
        },
        stdio: ["ignore", "pipe", "pipe"],
      },
    );
    return git("rev-parse", "HEAD");
  };
  git("init", "-q");
  write("site.config.json", { repository });
  return { root, git, write, submission, commit };
}

test("local generation reads the checkout without admission data or network", (t) => {
  const data = fixture(t);
  data.submission("2026-10-12-candidate-proof");
  const commit = data.commit("2026-10-12T11:00:00Z");
  const previousFetch = globalThis.fetch;
  globalThis.fetch = () => {
    throw Error("Catalogue generation must not use the network");
  };
  t.after(() => {
    globalThis.fetch = previousFetch;
  });
  const catalogue = buildSubmissionCatalogue({ root: data.root });
  const [record] = catalogue.records;
  assert.equal(record.status, "accepted");
  assert.deepEqual(record.theta, { numerator: "7", denominator: "8" });
  assert.equal(record.timeline_at, "2026-10-12T00:00:00Z");
  assert.equal(record.date_label, "Public announcement");
  assert.equal(record.source_introduced_at, undefined);
  assert.equal(record.submitted_at, "");
  assert.equal(record.first_verified_at, "");
  assert.equal(record.certificate_url, undefined);
  assert.equal(record.source_commit, commit);
  assert.match(record.solution_url, new RegExp(`/blob/${commit}/submissions/`));
  assert.equal(existsSync(join(data.root, ".work")), false);
  assert.deepEqual(
    JSON.parse(readFileSync(join(data.root, "catalogue/results.json"))),
    catalogue,
  );
  assert.equal(
    readSubmissions(data.root).get("candidate-proof").title,
    metadata.title,
  );

  // Branches and local edits are valid previews of exactly that checkout.
  data.git("checkout", "-qb", "feature/local-preview");
  data.submission("2026-10-13-new-proof", { source: theorem("3 / 4") });
  const preview = buildSubmissionCatalogue({ root: data.root });
  assert.equal(preview.records.length, 2);
  assert.equal(
    preview.records.find((r) => r.id === "new-proof").status,
    "accepted",
  );
  assert.equal(
    preview.records.find((r) => r.id === "new-proof").historical,
    undefined,
  );
  assert.equal(
    preview.records.find((r) => r.id === "new-proof").source_commit,
    "",
  );
  assert.equal(
    preview.records.find((r) => r.id === "new-proof").solution_url,
    undefined,
  );
});

test("local source edits do not borrow a pinned HEAD URL or commit", (t) => {
  const data = fixture(t);
  const directory = "2026-10-12-candidate-proof";
  data.submission(directory, {
    metadata: { ...metadata, references: [] },
  });
  const commit = data.commit("2026-10-12T11:00:00Z");
  // A metadata correction leaves the pinned Lean solution accurate.
  data.write(`submissions/${directory}/metadata.json`, {
    ...metadata,
    title: "Corrected title",
    references: [],
  });
  const [corrected] = buildSubmissionCatalogue({ root: data.root }).records;
  assert.equal(corrected.source_commit, commit);
  assert.equal(typeof corrected.solution_url, "string");

  data.write(
    `submissions/${directory}/src/Candidate/Main.lean`,
    theorem("3 / 4"),
  );
  const [edited] = buildSubmissionCatalogue({ root: data.root }).records;
  assert.equal(edited.source_commit, "");
  assert.equal(edited.solution_url, undefined);
  assert.deepEqual(edited.references, [
    { label: "Repository", url: `https://github.com/${repository}` },
  ]);

  // Staged changes and new supporting source also differ from HEAD.
  data.git("add", ".");
  assert.equal(
    buildSubmissionCatalogue({ root: data.root }).records[0].source_commit,
    "",
  );
  data.git("reset", "--hard", "-q", "HEAD");
  data.write(
    `submissions/${directory}/src/Candidate/Extra.lean`,
    "-- New source\n",
  );
  assert.equal(
    buildSubmissionCatalogue({ root: data.root }).records[0].solution_url,
    undefined,
  );
});

test("a shallow main-only clone builds without caches, history walks or network", (t) => {
  const data = fixture(t);
  data.submission("2026-10-12-candidate-proof");
  data.commit("2026-10-12T08:00:00Z");
  data.submission("2026-10-13-child-proof", {
    metadata: { ...metadata, builds_on: ["candidate-proof"] },
    source: theorem("3 / 4"),
  });
  data.commit("2026-10-13T08:00:00Z");
  const destination = mkdtempSync(join(tmpdir(), "qrh-clean-clone-"));
  t.after(() => rmSync(destination, { recursive: true, force: true }));
  execFileSync("git", [
    "clone",
    "-q",
    "--depth=1",
    "--single-branch",
    pathToFileURL(data.root).href,
    destination,
  ]);
  assert.equal(
    execFileSync("git", ["rev-parse", "--is-shallow-repository"], {
      cwd: destination,
      encoding: "utf8",
    }).trim(),
    "true",
  );
  const trace = join(destination, "git.trace");
  const previousTrace = process.env.GIT_TRACE;
  const previousFetch = globalThis.fetch;
  process.env.GIT_TRACE = trace;
  globalThis.fetch = () => {
    throw Error("Catalogue generation must not use the network");
  };
  let catalogue;
  try {
    catalogue = buildSubmissionCatalogue({ root: destination });
  } finally {
    if (previousTrace === undefined) delete process.env.GIT_TRACE;
    else process.env.GIT_TRACE = previousTrace;
    globalThis.fetch = previousFetch;
  }
  assert.equal(catalogue.records.length, 2);
  assert.equal(existsSync(join(destination, ".work")), false);
  assert.doesNotMatch(
    readFileSync(trace, "utf8"),
    /built-in: git[^\n]*\b(?:log|rev-list|merge-base|fetch)\b/,
  );
});

test("canonical bound reading ignores comments, strings and bound_sharp", (t) => {
  const data = fixture(t);
  data.submission("2026-10-12-candidate-proof", {
    source: `
/- theorem bound (hs : (1 / 2 : ℝ) < s.re) := /- nested -/ sorry -/
-- theorem bound (hs : (1 / 3 : ℝ) < s.re) := sorry
def example := "theorem bound (hs : (1 / 4 : ℝ) < s.re) := sorry"
theorem bound_sharp (hs : (1 / 5 : ℝ) < s.re) := existing_sharp
${theorem("14 / 16")}`,
  });
  assert.deepEqual(
    submissionBound(
      join(data.root, "submissions/2026-10-12-candidate-proof/src"),
    ).theta,
    { numerator: "7", denominator: "8" },
  );
});

test("canonical bound reading follows an explicit imported local export", (t) => {
  const data = fixture(t);
  const directory = "2026-10-12-candidate-proof";
  data.submission(directory, {
    source:
      "import Submissions.Original.Main\nnamespace Candidate\nexport Submissions.Original (bound)\nend Candidate\n",
  });
  data.write(
    `submissions/${directory}/src/Submissions/Original/Main.lean`,
    theorem("123456789123456789 / 246913578246913578"),
  );
  assert.deepEqual(
    submissionBound(join(data.root, `submissions/${directory}/src`)).theta,
    { numerator: "1", denominator: "2" },
  );
  data.write(
    `submissions/${directory}/src/Candidate/Main.lean`,
    "export Submissions.Original.Main (bound)\n",
  );
  assert.throws(
    () => submissionBound(join(data.root, `submissions/${directory}/src`)),
    /explicitly imported/,
  );
});

test("canonical bound reading permits renamed Unicode hypothesis and complex binders", (t) => {
  const data = fixture(t);
  data.submission("2026-10-12-candidate-proof", {
    source: theorem()
      .replaceAll(/\bhs\b/g, "hσ")
      .replaceAll(/\bs\b/g, "z₀"),
  });
  assert.deepEqual(
    submissionBound(
      join(data.root, "submissions/2026-10-12-candidate-proof/src"),
    ).theta,
    { numerator: "7", denominator: "8" },
  );
});

test("an exact algebraic bound is read with its proved rational upper bound", (t) => {
  const data = fixture(t);
  const directory = "2026-10-12-candidate-proof";
  const witness = `
theorem bound_le : ((777 - Real.sqrt 1081) / 852 : ℝ) ≤ (7 / 8 : ℝ) := by
  exact existing_le`;
  data.submission(directory, {
    source: theorem("(777 - Real.sqrt 1081) / 852") + witness,
  });
  const src = join(data.root, `submissions/${directory}/src`);
  assert.equal(submissionBound(src).theta_exact, "(777 − √1081) / 852 ≤ 7/8");
  data.submission(directory, {
    source: theorem("(777 - Real.sqrt 1081) / 852"),
  });
  assert.throws(() => submissionBound(src), /bound_le/);
});

test("directory migrations use the current path without inspecting old commits", (t) => {
  const data = fixture(t);
  data.submission("candidate-proof");
  data.commit(
    "2026-10-12T08:09:10Z",
    "Merge pull request #42 from author/proof",
  );
  data.git(
    "mv",
    "submissions/candidate-proof",
    "submissions/2026-10-12-candidate-proof",
  );
  const head = data.commit(
    "2026-10-27T08:00:00Z",
    "Organize submissions by date",
  );
  const [record] = buildSubmissionCatalogue({ root: data.root }).records;
  assert.equal(record.source_introduced_at, undefined);
  assert.equal(record.timeline_at, "2026-10-12T00:00:00Z");
  assert.equal(record.historical, undefined);
  assert.equal(record.pr, null);
  assert.equal(record.source_commit, head);
  assert.match(
    record.solution_url,
    /submissions\/2026-10-12-candidate-proof\/src\//,
  );
});

test("missing publication dates preserve the directory date without guessing historical status", (t) => {
  const data = fixture(t);
  data.submission("2026-10-08-candidate-proof");
  data.commit("2026-11-02T10:00:00Z");
  const [record] = buildSubmissionCatalogue({ root: data.root }).records;
  assert.equal(record.historical, undefined);
  assert.equal(record.timeline_at, "2026-10-08T00:00:00Z");
  assert.equal(record.date_label, "Public announcement");
  assert.equal(record.submitted_at, "");
  assert.equal(record.first_verified_at, "");
});

test("legacy metadata remains authoritative and generates its original certificate", (t) => {
  const data = fixture(t);
  const legacy = {
    id: "legacy-proof",
    title: "Original legacy result",
    theta: { numerator: "7", denominator: "8" },
    authors: [{ name: "Legacy Author" }],
    method: "Original documented method.",
    license: "Apache-2.0",
    builds_on: [],
    references: metadata.references,
    status: "framework-verified",
    timeline_at: "2026-10-10T00:00:00Z",
    submitted_at: "2026-10-10T08:00:00Z",
    first_verified_at: "2026-10-10T12:00:00Z",
    date_label: "Verification",
    verification_note: "Original verification context.",
    source_commit: "c".repeat(40),
    repository,
    certificate_url: "certificates/legacy-proof.json",
    verification: {
      report_url: `https://github.com/${repository}/actions/runs/10`,
      report_sha256: "d".repeat(64),
    },
  };
  data.submission("2026-10-10-legacy-proof", {
    metadata: legacy,
    source: "-- older source\n",
  });
  data.commit("2026-10-14T10:00:00Z");
  const [record] = buildSubmissionCatalogue({ root: data.root }).records;
  assert.equal(record.first_verified_at, legacy.first_verified_at);
  assert.equal(record.source_commit, legacy.source_commit);
  assert.equal(record.verification_note, legacy.verification_note);
  assert.equal(record.timeline_at, legacy.timeline_at);
  const saved = JSON.parse(
    readFileSync(join(data.root, "public/certificates/legacy-proof.json")),
  );
  assert.equal(saved.verified_at, legacy.first_verified_at);
  assert.equal(saved.source_commit, legacy.source_commit);
});

test("a documented announcement is precise in shallow checkouts and independent of verification", (t) => {
  const data = fixture(t);
  data.submission("2026-10-08-candidate-proof", {
    metadata: {
      ...metadata,
      published_at: "2026-10-08T18:48:49Z",
      references: [
        {
          label: "Result commit",
          url: "https://github.com/example/proof/commit/" + "a".repeat(40),
        },
      ],
    },
  });
  data.commit("2026-11-04T12:00:00Z");
  data.write(".git/shallow", data.git("rev-parse", "HEAD") + "\n");
  const [record] = buildSubmissionCatalogue({ root: data.root }).records;
  assert.equal(record.published_at, "2026-10-08T18:48:49Z");
  assert.equal(record.timeline_at, record.published_at);
  assert.equal(record.date_label, "Public announcement");
  assert.equal(record.historical, undefined);
  assert.equal(record.status, "accepted");
  assert.equal(record.first_verified_at, "");
  assert.equal(record.submitted_at, "");
});
