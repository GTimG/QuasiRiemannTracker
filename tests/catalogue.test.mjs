import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
  validateCatalogue,
  verifiedHere,
  timelineRecords,
} from "../core/catalogue.mjs";
import { frontierHistory, cmp } from "../core/rational.mjs";
import {
  EXTERNAL_PINS,
  validateExternalKernelEvidence,
} from "../core/external-kernel-evidence.mjs";
const data = () => JSON.parse(readFileSync("catalogue/results.json", "utf8"));
test("all five results advance the plotted frontier while verification stays separate", () => {
  const d = validateCatalogue(data());
  assert.equal(d.records.length, 5);
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
  const frontier = frontierHistory(timelineRecords(d.records), []);
  assert.equal(frontier.length, 5);
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
  e.records[1].first_verified_at = "2026-10-09T00:00:00Z";
  assert.throws(() => validateCatalogue(e), /Pending result/);
});
