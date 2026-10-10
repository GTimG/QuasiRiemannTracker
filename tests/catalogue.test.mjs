import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
  validateCatalogue,
  verifiedHere,
  timelineRecords,
} from "../core/catalogue.mjs";
import { frontierHistory, recordHistory, cmp } from "../core/rational.mjs";
import {
  EXTERNAL_PINS,
  validateExternalKernelEvidence,
} from "../core/external-kernel-evidence.mjs";
const data = () => JSON.parse(readFileSync("catalogue/results.json", "utf8"));
test("the existing contribution selects one current proof revision and preserves its earlier metadata", () => {
  const d = validateCatalogue(data());
  const current = d.records.filter((r) => r.id.startsWith("nielstron-"));
  assert.equal(current.length, 1);
  assert.equal(current[0].id, "nielstron-20261009-tightening");
  assert.equal(current[0].proof_revision, "nielstron-algebraic-20261009");
  assert.equal(d.historical_records.length, 1);
  assert.equal(d.historical_records[0].theta.numerator, "874957019420098946128604623");
  assert.equal(d.historical_records[0].source_commit, "49331e02e2c04bb2388ae9c6e9ea424c23b96ac6");
});
test("non-record alternatives retain the plotted frontier while verification stays separate", () => {
  const d = validateCatalogue(data());
  assert.equal(d.records.length, 6);
  const verified = d.records.filter(verifiedHere);
  validateExternalKernelEvidence(process.cwd(), d);
  assert.deepEqual(
    verified.map((r) => r.id),
    d.records
      .filter(
        (r) =>
          [
            "openai-baseline",
            "proofcouncil-20261009",
            "nielstron-20261009-tightening",
          ].includes(r.id) ||
          (EXTERNAL_PINS.entries[r.id] !== undefined &&
            EXTERNAL_PINS.entries[r.id] !== null),
      )
      .map((r) => r.id),
  );
  const alternativeId = "single-prime-29-33-20261010";
  const earlier = d.records.filter((r) => r.id !== alternativeId);
  const previousFrontier = frontierHistory(timelineRecords(earlier), []);
  const timeline = timelineRecords(d.records);
  const frontier = frontierHistory(timeline, []);
  assert.equal(frontier.length, 6);
  assert.deepEqual(frontier.slice(0, -1), previousFrontier);
  assert.equal(cmp(frontier.at(-1).theta, previousFrontier.at(-1).theta), 0);
  const alternative = recordHistory(timeline).find(
    (r) => r.id === alternativeId,
  );
  assert.equal(alternative.is_record, false);
  assert.equal(verifiedHere(alternative), false);
  assert.equal(cmp(alternative.theta, { numerator: "7", denominator: "8" }), 1);
  for (let i = 1; i < previousFrontier.length; i++) {
    assert.equal(
      cmp(previousFrontier[i].theta, previousFrontier[i - 1].theta),
      -1,
    );
  }
  assert.ok(
    d.records
      .filter((r) => !verifiedHere(r))
      .every((r) => r.first_verified_at === ""),
  );
});
test("Liu's algebraic threshold is enclosed exactly; a truncated decimal is rejected", () => {
  const d = data();
  validateCatalogue(d);
  const liu = d.records.find((r) => r.id.startsWith("liu-"));
  liu.theta = { numerator: "874957069799", denominator: "1000000000000" };
  liu.bound_interval.upper = liu.theta;
  assert.throws(() => validateCatalogue(d), /enclosure/);
});
test("catalogue cannot fabricate signed admission or local verification dates for pending results", () => {
  const d = data();
  d.records[1].status = "verified";
  assert.throws(() => validateCatalogue(d), /cannot mint/);
  const e = data();
  e.records[1].first_verified_at = "2026-10-09T00:00:00Z";
  assert.throws(() => validateCatalogue(e), /Pending result/);
});
