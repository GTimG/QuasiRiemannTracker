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
import { dirname, join } from "node:path";
import { pathToFileURL } from "node:url";
import { readLocalPublications } from "../scripts/local-publications.mjs";
import { buildSubmissionCatalogue } from "../scripts/submission-catalogue.mjs";
import { KERNELS } from "../verifier/certificate.mjs";

const repository = "owner/repository";
const ids = ["ordinary-proof", "historical-proof"];

function git(root, ...args) {
  return execFileSync("git", args, {
    cwd: root,
    encoding: "utf8",
    stdio: ["ignore", "pipe", "pipe"],
  }).trim();
}

function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), "qrh-local-publications-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const write = (path, value) => {
    const target = join(root, path);
    mkdirSync(dirname(target), { recursive: true });
    writeFileSync(
      target,
      typeof value === "string" ? value : JSON.stringify(value),
    );
  };
  const commit = (message) => {
    git(root, "add", ".");
    git(
      root,
      "-c",
      "user.name=Test",
      "-c",
      "user.email=test@example.com",
      "commit",
      "-qm",
      message,
    );
    return git(root, "rev-parse", "HEAD");
  };
  git(root, "init", "-q", "--initial-branch=main");
  write("site.config.json", { repository });
  const mainParent = commit("Initialize main");
  for (const [id, date, bound] of [
    [ids[0], "2026-10-12", "7 / 8"],
    [ids[1], "2026-10-08", "4 / 5"],
  ]) {
    const directory = `submissions/${date}-${id}`;
    write(`${directory}/metadata.json`, {
      title: id,
      authors: [{ name: "Original Author" }],
      description: "The original author's proof and attribution.",
      license: "Apache-2.0",
      references: [
        { label: "Original source", url: "https://example.com/proof" },
      ],
    });
    write(
      `${directory}/src/Candidate/Main.lean`,
      `namespace Candidate
theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (${bound} : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  exact original_proof χ hs hpole
end Candidate
`,
    );
  }
  const mainTip = commit("Add the two checked-out submissions");

  // The archive is a separate root. Its latest tree retains earlier records,
  // although a depth-one clone cannot inspect either branch's parent commit.
  git(root, "checkout", "-q", "--orphan", "admission-records");
  git(root, "rm", "-rf", "--quiet", ".");
  const envelope = (id, overrides = {}) => ({
    result_id: id,
    number: id === ids[0] ? 42 : 43,
    source_path: `submissions/${id}/src`,
    pr: {
      created_at:
        id === ids[0] ? "2026-10-12T10:15:00Z" : "2026-11-02T12:00:00Z",
    },
    certificate: {
      schema_version: 1,
      result_id: id,
      theta_exact: id === ids[0] ? "7/8" : "4/5",
      verified_at:
        id === ids[0] ? "2026-10-12T12:34:56Z" : "2026-11-02T13:00:00Z",
      source_repository: repository,
      source_commit: "a".repeat(40),
      report_sha256: "b".repeat(64),
      report_url: `https://github.com/${repository}/actions/runs/123`,
      kernels: KERNELS,
      ...overrides,
    },
  });
  const early = envelope(ids[0]);
  const historical = envelope(ids[1]);
  write("records/ordinary-early.json", early);
  write("records/historical.json", historical);
  const archiveParent = commit("Record original publication facts");
  write(
    "records/ordinary-rerun.json",
    envelope(ids[0], { verified_at: "2026-10-15T09:00:00Z" }),
  );
  write(
    "records/ordinary-other-bound.json",
    envelope(ids[0], {
      theta_exact: "3/4",
      verified_at: "2026-10-10T09:00:00Z",
    }),
  );
  write("records/archive-only.json", envelope("unmerged-proof"));
  commit("Retain old facts and add a rerun and another statement");
  git(root, "checkout", "-q", "main");
  return { root, mainParent, mainTip, archiveParent, early, historical };
}

function shallowClone(t, source, allBranches = true) {
  const root = mkdtempSync(join(tmpdir(), "qrh-publication-clone-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  git(
    root,
    "clone",
    "-q",
    "--depth=1",
    allBranches ? "--no-single-branch" : "--single-branch",
    "--branch=main",
    pathToFileURL(source).href,
    root,
  );
  assert.equal(git(root, "rev-parse", "--is-shallow-repository"), "true");
  return root;
}

function noNetwork(t) {
  const previousFetch = globalThis.fetch;
  globalThis.fetch = () => {
    throw Error("Publication facts must come from local branch tips");
  };
  t.after(() => {
    globalThis.fetch = previousFetch;
  });
}

test("a shallow clone retains first publication facts from the current archive tree", (t) => {
  const source = fixture(t);
  noNetwork(t);
  const full = buildSubmissionCatalogue({ root: source.root });
  const clone = shallowClone(t, source.root);
  for (const parent of [source.mainParent, source.archiveParent])
    assert.throws(() => git(clone, "cat-file", "-e", parent));
  assert.equal(git(clone, "rev-list", "--count", "main"), "1");
  assert.equal(
    git(clone, "rev-list", "--count", "origin/admission-records"),
    "1",
  );

  // These intentionally minimal envelopes contain no admission record,
  // report JSON, source inventory or original proof objects to revalidate.
  const publications = readLocalPublications(clone);
  assert.equal(publications[ids[0]].length, 3);
  assert.equal(publications[ids[0]][0].certificate.theta_exact, "3/4");
  const shallow = buildSubmissionCatalogue({ root: clone });
  assert.deepEqual(shallow, full);
  assert.equal(shallow.records.length, 2);
  assert.equal(
    shallow.records.some((record) => record.id === "unmerged-proof"),
    false,
  );
  const ordinary = shallow.records.find((record) => record.id === ids[0]);
  assert.equal(ordinary.status, "framework-verified");
  assert.equal(ordinary.pr, source.early.number);
  assert.equal(ordinary.submitted_at, source.early.pr.created_at);
  assert.equal(ordinary.timeline_at, source.early.pr.created_at);
  assert.equal(ordinary.historical, undefined);
  assert.equal(
    ordinary.first_verified_at,
    source.early.certificate.verified_at,
  );
  assert.equal(ordinary.source_commit, source.early.certificate.source_commit);
  assert.equal(
    ordinary.solution_url,
    `https://github.com/${repository}/blob/${source.early.certificate.source_commit}/${source.early.source_path}/Candidate/Main.lean`,
  );
  assert.deepEqual(
    JSON.parse(
      readFileSync(join(clone, "public/certificates/ordinary-proof.json")),
    ),
    source.early.certificate,
  );
  const historical = shallow.records.find((record) => record.id === ids[1]);
  assert.equal(historical.historical, undefined);
  assert.equal(historical.timeline_at, source.historical.pr.created_at);
  assert.equal(historical.date_label, "PR submitted");
  assert.equal(historical.submitted_at, source.historical.pr.created_at);
  assert.equal(
    historical.first_verified_at,
    source.historical.certificate.verified_at,
  );
  assert.equal(existsSync(join(clone, "catalogue/provenance.json")), false);
  assert.equal(existsSync(join(clone, ".work")), false);
});

test("a main-only shallow clone includes every submission without archive facts", (t) => {
  const source = fixture(t);
  const clone = shallowClone(t, source.root, false);
  noNetwork(t);
  assert.throws(() => git(clone, "cat-file", "-e", source.mainParent));
  assert.throws(() =>
    git(clone, "rev-parse", "--verify", "origin/admission-records"),
  );
  assert.deepEqual(readLocalPublications(clone), {});
  const catalogue = buildSubmissionCatalogue({ root: clone });
  assert.equal(catalogue.records.length, 2);
  for (const record of catalogue.records) {
    assert.equal(record.status, "accepted");
    assert.equal(record.submitted_at, "");
    assert.equal(record.first_verified_at, "");
    assert.equal(record.certificate_url, undefined);
    assert.equal(record.historical, undefined);
    assert.equal(record.pr, null);
    assert.equal(record.date_label, "Source created");
    assert.equal(record.source_commit, source.mainTip);
  }
  assert.equal(
    catalogue.records.find((record) => record.id === ids[1]).timeline_at,
    "2026-10-08T00:00:00Z",
  );
});
