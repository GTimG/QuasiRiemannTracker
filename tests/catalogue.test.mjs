import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
  validateCatalogue,
  verifiedHere,
  timelineRecords,
  historicalBaseline,
  statusLabel,
  formatContributionDate,
} from "../core/catalogue.mjs";
import { frontierHistory, cmp } from "../core/rational.mjs";
const data = () => JSON.parse(readFileSync("catalogue/results.json", "utf8"));
test("the classical baseline and results advance the frontier while verification stays separate", () => {
  const d = validateCatalogue(data());
  assert.equal(d.records.length, 6);
  const verified = d.records.filter(verifiedHere);
  assert.deepEqual(
    verified.map((r) => r.id),
    ["openai-baseline", "proofcouncil-20261009", "nielstron-20261009-tightening"],
  );
  const frontier = frontierHistory(timelineRecords(d.records), []);
  assert.equal(frontier.length, d.records.length);
  for (let i = 0; i < frontier.length; i++) {
    assert.equal(cmp(frontier[i].theta, d.records[i].theta), 0);
    if (i) assert.equal(cmp(frontier[i].theta, frontier[i - 1].theta), -1);
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
  e.records[1].status = "verification-pending";
  e.records[1].first_verified_at = "2026-10-09T00:00:00Z";
  assert.throws(() => validateCatalogue(e), /Pending result/);
});

test("historical baseline preserves date precision and cannot claim verification or a tighter bound", () => {
  const d = data();
  const baseline = d.records.find(historicalBaseline);
  assert.ok(baseline);
  assert.equal(verifiedHere(baseline), false);
  assert.equal(statusLabel(baseline), "Historical baseline");
  assert.equal(formatContributionDate(baseline), "1922");
  assert.equal(cmp(baseline.theta, { numerator: "1", denominator: "1" }), 0);
  for (const changes of [
    { first_verified_at: "2026-10-10T00:00:00Z" },
    { receipt_url: "proofs/fake-receipt.json" },
    { theta: { numerator: "7", denominator: "8" } },
  ]) {
    const changed = data();
    Object.assign(changed.records.find(historicalBaseline), changes);
    assert.throws(() => validateCatalogue(changed), /Historical baseline/);
  }
  baseline.timeline_at = "1922-02-15T00:00:00Z";
  assert.throws(() => validateCatalogue(d), /Year-only dates/);
});
