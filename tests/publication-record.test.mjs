import test from "node:test";
import assert from "node:assert/strict";
import {
  publicationRecord,
  validatePublication,
} from "../verifier/publication-record.mjs";
import { record } from "./fixtures/catalogue.mjs";

function fixture() {
  return {
    catalogue: { schema_version: 1, records: [record()] },
    admission: {
      result_id: "candidate-proof",
      theta_exact: "4/5",
      repository: "example/proofs",
      number: 20,
      head_sha: "a".repeat(40),
      source_path: "submissions/candidate-proof/src",
      metadata: {
        title: "Example improvement",
        authors: [{ name: "Example author" }],
        description: "A synthetic independently checked theorem.",
        builds_on: ["fixture-baseline"],
      },
      pr: { created_at: "2030-10-03T13:00:00Z" },
      certificate: {
        schema_version: 1,
        result_id: "candidate-proof",
        theta_exact: "4/5",
        verified_at: "2030-10-04T00:00:00Z",
        source_repository: "example/proofs",
        source_commit: "a".repeat(40),
        kernels: ["Lean default", "nanoda", "con-ron"],
        report_sha256: "b".repeat(64),
        report_url:
          "https://github.com/example/proofs/actions/runs/1234/attempts/1",
      },
    },
  };
}

test("admission uses the same publication record that a later build generates", () => {
  const { catalogue, admission } = fixture();
  const validated = validatePublication(catalogue, admission);
  assert.deepEqual(validated, publicationRecord(admission));
  assert.equal(validated.method, admission.metadata.description);
  assert.deepEqual(validated.builds_on, ["fixture-baseline"]);
  assert.equal(validated.timeline_at, admission.pr.created_at);
  assert.equal(validated.historical, undefined);
  assert.equal(validated.date_label, "Public announcement");
  assert.equal(validated.first_verified_at, admission.certificate.verified_at);
  assert.equal(
    catalogue.records.length,
    1,
    "validation does not mutate its snapshot",
  );
});

test("publication links follow the immutable dated source path while IDs remain stable", () => {
  const { catalogue, admission } = fixture();
  admission.source_path = "submissions/2030-10-03-candidate-proof/src";
  const published = validatePublication(catalogue, admission);
  assert.equal(published.id, "candidate-proof");
  assert.equal(published.certificate_url, "certificates/candidate-proof.json");
  assert.equal(
    published.solution_url,
    `https://github.com/example/proofs/blob/${admission.head_sha}/submissions/2030-10-03-candidate-proof/src/Candidate/Main.lean`,
  );
  admission.source_path = "submissions/2030-10-03-another-proof/src";
  assert.throws(
    () => publicationRecord(admission),
    /differs from its verified source/,
  );
});

for (const scenario of ["unknown", "later", "same-time"])
  test(`a ${scenario} predecessor cannot enter the published graph`, () => {
    const { catalogue, admission } = fixture();
    if (scenario === "unknown")
      admission.metadata.builds_on = ["unpublished-proof"];
    else
      catalogue.records[0].timeline_at =
        scenario === "later" ? "2030-10-05T00:00:00Z" : admission.pr.created_at;
    assert.throws(
      () => validatePublication(catalogue, admission),
      /Unknown or later catalogue predecessor/,
    );
  });

test("duplicate IDs include immutable historical proof revisions", () => {
  const { catalogue, admission } = fixture();
  catalogue.records[0].proof_revision = "current-revision";
  catalogue.historical_records = [
    record({ timeline_at: "2030-09-30T00:00:00Z" }),
    record({
      proof_revision: "candidate-proof",
      timeline_at: "2030-10-01T00:00:00Z",
    }),
  ];
  assert.throws(
    () => validatePublication(catalogue, admission),
    /Result ID already published/,
  );
});

test("unsupported algebraic values fail before they can be archived", () => {
  const { catalogue, admission } = fixture();
  admission.theta_exact = admission.certificate.theta_exact = "sqrt(2)/2";
  admission.certificate.bound_interval = {
    lower: { numerator: "7", denominator: "10" },
    upper: { numerator: "71", denominator: "100" },
  };
  assert.throws(
    () => validatePublication(catalogue, admission),
    /Unsupported algebraic expression/,
  );
});

test("an algebraic value without a certified enclosure cannot be published", () => {
  const { catalogue, admission } = fixture();
  admission.theta_exact = admission.certificate.theta_exact =
    "(1507 − 2√921) / 1653";
  assert.throws(
    () => validatePublication(catalogue, admission),
    /Missing exact bound enclosure/,
  );
});

test("an invalid enclosure for a supported value is rejected before publication", () => {
  const { catalogue, admission } = fixture();
  admission.theta_exact = admission.certificate.theta_exact =
    "(1507 − 2√921) / 1653";
  admission.certificate.bound_interval = {
    lower: { numerator: "7", denominator: "10" },
    upper: { numerator: "71", denominator: "100" },
  };
  assert.throws(
    () => validatePublication(catalogue, admission),
    /Invalid certified enclosure/,
  );
});

test("admission normalizes documented announcements without historical website flags", () => {
  const { catalogue, admission } = fixture();
  admission.metadata.builds_on = [];
  admission.metadata.published_at = "2030-10-01T18:48:49Z";
  admission.source_path = "submissions/2030-10-01-candidate-proof/src";
  const published = validatePublication(catalogue, admission);
  assert.equal(published.historical, undefined);
  assert.equal(published.published_at, admission.metadata.published_at);
  assert.equal(published.timeline_at, admission.metadata.published_at);
  assert.equal(published.date_label, "Public announcement");
  assert.equal(published.submitted_at, admission.pr.created_at);
  assert.equal(published.first_verified_at, admission.certificate.verified_at);
  delete admission.metadata.published_at;
  assert.equal(
    publicationRecord(admission).published_at,
    admission.pr.created_at,
  );
  admission.source_path = "submissions/2030-10-04-candidate-proof/src";
  assert.throws(() => publicationRecord(admission), /cannot be after/);
});
