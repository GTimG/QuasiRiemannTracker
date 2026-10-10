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
test("the existing contribution selects one current proof revision and preserves its earlier metadata", () => {
  const d = validateCatalogue(data());
  const current = d.records.filter((r) => r.id.startsWith("nielstron-"));
  assert.equal(current.length, 1);
  assert.equal(current[0].id, "nielstron-20261009-tightening");
  assert.equal(current[0].proof_revision, "nielstron-algebraic-20261009");
  assert.equal(d.historical_records.length, 1);
  assert.equal(
    d.historical_records[0].theta.numerator,
    "874957019420098946128604623",
  );
  assert.equal(
    d.historical_records[0].source_commit,
    "49331e02e2c04bb2388ae9c6e9ea424c23b96ac6",
  );
});
test("the plotted frontier retains the strongest bound while verification stays separate", () => {
  const d = validateCatalogue(data());
  assert.equal(d.records.length, 7);
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
            "akashlevy-20261009-weighted-numerator",
            "cycle25-quartic-20261010",
          ].includes(r.id) ||
          (EXTERNAL_PINS.entries[r.id] !== undefined &&
            EXTERNAL_PINS.entries[r.id] !== null),
      )
      .map((r) => r.id),
  );
  const frontier = frontierHistory(timelineRecords(d.records), []);
  assert.equal(frontier.length, 7);
  for (let i = 0; i < frontier.length; i++) {
    assert.ok(cmp(frontier[i].theta, d.records[i].theta) <= 0);
    if (i) assert.ok(cmp(frontier[i].theta, frontier[i - 1].theta) <= 0);
  }
  const strongest = d.records.reduce((best, r) =>
    cmp(r.theta, best.theta) < 0 ? r : best,
  );
  assert.equal(cmp(frontier.at(-1).theta, strongest.theta), 0);
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
test("Cycle25 advances the boundary only after independent maintainer verification", () => {
  const d = validateCatalogue(data());
  const cycle = d.records.find((r) => r.id === "cycle25-quartic-20261010");
  assert.deepEqual(cycle.theta, {
    numerator: "683505193",
    denominator: "781250000",
  });
  assert.equal(cycle.status, "framework-verified");
  assert.equal(cycle.first_verified_at, "2026-10-10T16:09:09.733191+00:00");
  assert.equal(verifiedHere(cycle), true);
  assert.deepEqual(cycle.builds_on, [
    "openai-baseline",
    "akashlevy-20261009-weighted-numerator",
  ]);
  assert.equal(
    cycle.entrypoint.declaration,
    "Cycle25.dirichlet_nonzero_catalogue",
  );
  const frontier = frontierHistory(timelineRecords(d.records), []);
  assert.equal(cmp(frontier.at(-1).theta, cycle.theta), 0);
  assert.equal(d.records.filter(verifiedHere).length, 7);
  assert.ok(cycle.references.some((r) => r.url.endsWith("/paper.pdf")));
  assert.ok(
    cycle.references.some((r) => r.url.endsWith("/source-public.tar.gz")),
  );
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
