import test from "node:test";
import assert from "node:assert/strict";
import {
  validateCatalogue,
  verifiedHere,
  timelineRecords,
  historicalBaseline,
  statusLabel,
  formatContributionDate,
  withSubmissionTimeline,
} from "../core/catalogue.mjs";
import {
  catalogueProofRecords,
  findProofRevision,
} from "../core/catalogue-revisions.mjs";
import { frontierHistory, recordHistory, cmp } from "../core/rational.mjs";
import {
  catalogue,
  record,
  algebraicRecord,
  historicalRecord,
} from "./fixtures/catalogue.mjs";

const revisionCatalogue = () => {
  const original = record({ id: "fixture-revised" });
  const current = record({
    id: original.id,
    proof_revision: "fixture-revised-v2",
    theta: { numerator: "3", denominator: "4" },
    timeline_at: "2030-10-12T00:00:00Z",
    source_commit: "b".repeat(40),
  });
  return {
    schema_version: 1,
    records: [current],
    historical_records: [original],
  };
};

test("recorded PR dates determine the timeline without changing verification history or historical dates", () => {
  const original = record({ pr: 41 });
  const updated = withSubmissionTimeline(original);
  assert.equal(updated.timeline_at, original.submitted_at);
  assert.equal(updated.date_label, "PR submitted");
  assert.equal(updated.first_verified_at, original.first_verified_at);
  assert.equal(original.timeline_at, "2030-10-02T00:00:00Z");
  for (const value of [
    record({ pr: null }),
    record({ pr: 8, submitted_at: "" }),
    historicalRecord({ pr: 5, submitted_at: "" }),
  ])
    assert.deepEqual(withSubmissionTimeline(value), value);
});

test("a contribution displays its current revision and keeps the original proof metadata", () => {
  const data = validateCatalogue(revisionCatalogue());
  assert.deepEqual(
    data.records.map((r) => r.proof_revision),
    ["fixture-revised-v2"],
  );
  assert.deepEqual(
    catalogueProofRecords(data).map((r) => r.source_commit),
    ["b".repeat(40), "a".repeat(40)],
  );
  assert.equal(
    findProofRevision(data, "fixture-revised"),
    data.historical_records[0],
  );
  assert.equal(findProofRevision(data, "fixture-revised-v2"), data.records[0]);
});

test("revisions reject missing originals, duplicate proof IDs and reversed chronology", () => {
  const missing = revisionCatalogue();
  missing.historical_records = [];
  assert.throws(() => validateCatalogue(missing), /missing its original/);
  const duplicate = revisionCatalogue();
  duplicate.historical_records.push(
    structuredClone(duplicate.historical_records[0]),
  );
  assert.throws(() => validateCatalogue(duplicate), /Duplicate/);
  const reversed = revisionCatalogue();
  reversed.historical_records[0].timeline_at = reversed.records[0].timeline_at;
  assert.throws(() => validateCatalogue(reversed), /must precede/);
});

test("revision identity stays valid for future contributions and multiple older proofs", () => {
  const data = revisionCatalogue();
  data.historical_records.push(
    record({
      id: "fixture-revised",
      proof_revision: "fixture-revised-intermediate",
      timeline_at: "2030-10-10T00:00:00Z",
    }),
  );
  assert.equal(catalogueProofRecords(validateCatalogue(data)).length, 3);
  for (const value of ["", "../escape", "fixture-revised", 12]) {
    const invalid = revisionCatalogue();
    invalid.records[0].proof_revision = value;
    assert.throws(
      () => validateCatalogue(invalid),
      /Invalid catalogue proof revision/,
    );
  }
});

test("the frontier uses contribution dates, keeps stronger bounds, and excludes pending claims", () => {
  const data = catalogue();
  data.records.push(
    record({
      id: "fixture-later-weaker",
      theta: { numerator: "9", denominator: "10" },
      timeline_at: "2030-10-15T00:00:00Z",
    }),
  );
  data.records.push(
    record({
      id: "fixture-pending-stronger",
      status: "verification-pending",
      theta: { numerator: "1", denominator: "2" },
      timeline_at: "2030-10-16T00:00:00Z",
      first_verified_at: "",
    }),
  );
  validateCatalogue(data);
  const verified = data.records.filter(verifiedHere);
  const timeline = recordHistory(timelineRecords(verified));
  assert.deepEqual(
    timeline.map((r) => r.is_record),
    [true, true, true, false],
  );
  assert.deepEqual(
    timeline.map((r) => r.first_verified_at),
    verified.map((r) => r.timeline_at),
  );
  const frontier = frontierHistory(timeline, []);
  assert.deepEqual(
    frontier.map((r) => r.theta),
    [
      verified[0].theta,
      verified[1].theta,
      verified[2].theta,
      verified[2].theta,
    ],
  );
  assert.ok(cmp(frontier.at(-1).theta, data.records.at(-1).theta) > 0);
});

test("algebraic enclosures accept certified endpoints and reject truncated decimals", () => {
  const entry = algebraicRecord();
  validateCatalogue({ schema_version: 1, records: [entry] });
  entry.theta = { numerator: "874957069799", denominator: "1000000000000" };
  entry.bound_interval.upper = entry.theta;
  assert.throws(
    () => validateCatalogue({ schema_version: 1, records: [entry] }),
    /enclosure/,
  );
});

test("ambiguous comparisons require refined algebraic intervals", () => {
  const algebraic = algebraicRecord();
  const overlapping = record({ id: "fixture-overlap", theta: algebraic.theta });
  assert.throws(
    () =>
      validateCatalogue({
        schema_version: 1,
        records: [algebraic, overlapping],
      }),
    /Overlapping bound intervals/,
  );
});

test("validation rejects unsupported statuses and fabricated pending verification dates", () => {
  for (const [changes, error] of [
    [{ status: "verified" }, /Unsupported/],
    [{ status: "verification-pending" }, /Pending result/],
    [{ first_verified_at: "" }, /Missing framework check date/],
  ]) {
    assert.throws(
      () =>
        validateCatalogue({ schema_version: 1, records: [record(changes)] }),
      error,
    );
  }
});

test("validation rejects duplicate IDs, unsafe evidence and unknown or later predecessors", () => {
  for (const [records, error] of [
    [[record(), record()], /duplicate/i],
    [
      [
        record({
          references: [{ label: "Source", url: "javascript:alert(1)" }],
        }),
      ],
      /Unsafe reference/,
    ],
    [[record({ builds_on: ["unknown-result"] })], /Unknown or later/],
    [
      [
        record(),
        record({ id: "fixture-child", builds_on: ["fixture-baseline"] }),
      ],
      /Unknown or later/,
    ],
  ]) {
    assert.throws(
      () => validateCatalogue({ schema_version: 1, records }),
      error,
    );
  }
});

test("historical baselines retain year precision and their separate verification status", () => {
  const baseline = historicalRecord();
  validateCatalogue({ schema_version: 1, records: [baseline] });
  assert.equal(historicalBaseline(baseline), true);
  assert.equal(verifiedHere(baseline), false);
  assert.equal(statusLabel(baseline), "Historical baseline");
  assert.equal(formatContributionDate(baseline), "1922");
  assert.equal(formatContributionDate(record()), "02 Oct 2030");
});

test("historical baselines enforce theta one without local verification claims", () => {
  for (const changes of [
    { first_verified_at: "2030-10-10T00:00:00Z" },
    { receipt_url: "proofs/fake-receipt.json" },
    { log_url: "proofs/fake-log.json" },
    { theta: { numerator: "7", denominator: "8" } },
  ]) {
    assert.throws(
      () =>
        validateCatalogue({
          schema_version: 1,
          records: [historicalRecord(changes)],
        }),
      /Historical baseline must be theta = 1/,
    );
  }
  assert.throws(
    () =>
      validateCatalogue({
        schema_version: 1,
        records: [historicalRecord({ timeline_at: "1922-02-15T00:00:00Z" })],
      }),
    /start-of-year plotting anchor/,
  );
});

test("historical imported results keep their original timeline and normal verification status", () => {
  const original = record({
    historical: true,
    timeline_at: "2030-09-01T00:00:00Z",
    date_label: "Historical source created",
    submitted_at: "2030-10-03T12:00:00Z",
  });
  const published = withSubmissionTimeline(original);
  assert.equal(published.timeline_at, original.timeline_at);
  assert.equal(published.submitted_at, original.submitted_at);
  assert.equal(published.first_verified_at, original.first_verified_at);
  assert.equal(published.status, original.status);
  assert.equal(verifiedHere(published), true);
  validateCatalogue({ schema_version: 1, records: [published] });
  assert.throws(
    () =>
      validateCatalogue({
        schema_version: 1,
        records: [{ ...published, timeline_at: original.submitted_at }],
      }),
    /historical catalogue date/,
  );
  assert.throws(
    () =>
      validateCatalogue({
        schema_version: 1,
        records: [{ ...published, timeline_at: "2030-10-04T00:00:00Z" }],
      }),
    /cannot be after/,
  );
});

test("accepted checkout sources join the frontier without a fabricated verification date", () => {
  const accepted = record({
    id: "accepted-source",
    status: "accepted",
    theta: { numerator: "4", denominator: "5" },
    timeline_at: "2030-10-08T00:00:00Z",
    date_label: "Source created",
    first_verified_at: "",
    submitted_at: "",
    certificate_url: undefined,
    pr: 111,
  });
  const data = validateCatalogue({
    schema_version: 1,
    records: [record(), accepted],
  });
  assert.equal(statusLabel(accepted), "Verified in our framework");
  assert.equal(verifiedHere(accepted), true);
  assert.equal(accepted.first_verified_at, "");
  assert.deepEqual(withSubmissionTimeline(accepted), accepted);
  const timeline = recordHistory(
    timelineRecords(data.records.filter(verifiedHere)),
  );
  assert.deepEqual(
    timeline.map((result) => result.is_record),
    [true, true],
  );
  assert.deepEqual(frontierHistory(timeline, []).at(-1).theta, accepted.theta);
});

test("accepted historical sources require an actual recorded PR date", () => {
  const accepted = record({
    status: "accepted",
    historical: true,
    timeline_at: "2030-10-08T00:00:00Z",
    date_label: "Historical source created",
    first_verified_at: "",
    submitted_at: "2030-10-10T16:00:00Z",
    pr: 111,
  });
  const check = (changes = {}) =>
    validateCatalogue({
      schema_version: 1,
      records: [{ ...accepted, ...changes }],
    });
  assert.doesNotThrow(() => check());
  assert.throws(
    () => check({ timeline_at: "2030-10-11T00:00:00Z" }),
    /cannot be after/,
  );
  assert.throws(
    () => check({ timeline_at: "2030-10-10T00:00:00Z" }),
    /historical catalogue date/,
  );
  assert.throws(
    () => check({ submitted_at: "" }),
    /Missing valid PR submission date/,
  );
});

test("accepted attributions allow same-day predecessors without inventing a clock order", () => {
  const parent = record({
    id: "same-day-parent",
    timeline_at: "2030-10-08T18:00:00Z",
  });
  const child = record({
    id: "same-day-child",
    timeline_at: "2030-10-08T00:00:00Z",
    builds_on: [parent.id],
  });
  for (const accepted of [parent, child]) {
    const entries = [parent, child].map((entry) =>
      entry === accepted
        ? {
            ...entry,
            status: "accepted",
            first_verified_at: "",
            submitted_at: "",
          }
        : entry,
    );
    assert.doesNotThrow(() =>
      validateCatalogue({ schema_version: 1, records: entries }),
    );
    const withLaterParent = entries.map((entry) =>
      entry.id === parent.id
        ? {
            ...entry,
            timeline_at: "2030-10-09T00:00:00Z",
          }
        : entry,
    );
    assert.throws(
      () => validateCatalogue({ schema_version: 1, records: withLaterParent }),
      /Unknown or later/,
    );
  }
  for (const clock of ["2030-10-08T00:00:00Z", "2030-10-08T18:00:00Z"])
    assert.throws(
      () =>
        validateCatalogue({
          schema_version: 1,
          records: [{ ...parent, timeline_at: clock }, child],
        }),
      /Unknown or later/,
    );
  assert.doesNotThrow(() =>
    validateCatalogue({
      schema_version: 1,
      records: [
        { ...parent, timeline_at: "2030-10-09T00:30:00+02:00" },
        {
          ...child,
          status: "accepted",
          first_verified_at: "",
          submitted_at: "",
        },
      ],
    }),
  );
});

test("accepted same-day attribution graphs reject missing parents and cycles", () => {
  const accepted = (id, builds_on) =>
    record({
      id,
      status: "accepted",
      timeline_at: "2030-10-08T00:00:00Z",
      first_verified_at: "",
      submitted_at: "",
      builds_on,
    });
  for (const entries of [
    [accepted("self-cycle", ["self-cycle"])],
    [
      accepted("cycle-one", ["cycle-two"]),
      accepted("cycle-two", ["cycle-one"]),
    ],
  ])
    assert.throws(
      () => validateCatalogue({ schema_version: 1, records: entries }),
      /Cyclic catalogue predecessors/,
    );
  assert.throws(
    () =>
      validateCatalogue({
        schema_version: 1,
        records: [accepted("missing-parent", ["not-present"])],
      }),
    /Unknown or later/,
  );
});
