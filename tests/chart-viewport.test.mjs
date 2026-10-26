import assert from "node:assert/strict";
import test from "node:test";
import { chartExtent } from "../core/chart-viewport.mjs";
import { cmp } from "../core/rational.mjs";

const record = (
  id,
  date,
  numerator,
  denominator,
  status = "framework-verified",
) => ({
  id,
  timeline_at: `${date}T00:00:00Z`,
  first_verified_at: `${date}T00:00:00Z`,
  theta: { numerator, denominator },
  status,
});
const first = record("first", "2026-10-06", "7", "8");
const improved = record("improved", "2026-10-10", "8749", "10000");

test("default extent follows verified record improvements below one", () => {
  const additions = [
    record("historical", "1922-01-01", "1", "1", "historical-baseline"),
    record("verified-one", "2000-01-01", "1", "1"),
    record("weaker", "2034-01-01", "29", "33"),
    record("tie", "2040-01-01", "8749", "10000"),
    record("pending", "1859-01-01", "1", "2", "verification-pending"),
  ];
  assert.deepEqual(
    chartExtent(
      [...additions, improved, first],
      [],
      false,
      [0, 100],
      Date.parse(improved.timeline_at),
    ),
    {
      start: Date.parse("2026-10-05T00:00:00Z"),
      end: Date.parse("2026-10-11T00:00:00Z"),
      low: improved.theta,
      high: first.theta,
    },
  );
});

test("the fitted timeline includes the viewing time without widening the bound range", () => {
  const now = Date.parse("2026-10-20T12:00:00Z");
  const extent = chartExtent([first, improved], [], false, [0, 100], now);
  assert.ok(extent.start < Date.parse(first.timeline_at));
  assert.equal(extent.end, now + 86400000);
  assert.deepEqual(extent.low, improved.theta);
  assert.deepEqual(extent.high, first.theta);
});

test("full history includes historical, weaker and later results", () => {
  const historical = record(
    "historical",
    "1922-01-01",
    "1",
    "1",
    "historical-baseline",
  );
  const weaker = record("weaker", "2034-01-01", "29", "33");
  const extent = chartExtent([first, improved, historical, weaker], [], true);
  assert.ok(extent.start < Date.parse(historical.timeline_at));
  assert.ok(extent.end > Date.parse(weaker.timeline_at));
  assert.deepEqual(extent.low, improved.theta);
  assert.deepEqual(extent.high, historical.theta);
});

test("a withdrawal keeps the new active best and its frontier transition in view", () => {
  const withdrawn = record("withdrawn", "2027-01-01", "3", "4");
  const activeBest = record("active-best", "2034-01-01", "4", "5");
  const at = "2035-01-01T00:00:00Z";
  const extent = chartExtent(
    [first, withdrawn, activeBest],
    [{ type: "withdraw", id: withdrawn.id, at }],
  );
  assert.ok(extent.end > Date.parse(at));
  assert.ok(extent.start < Date.parse(activeBest.timeline_at));
  assert.ok(cmp(extent.low, activeBest.theta) <= 0);
  assert.ok(cmp(extent.high, activeBest.theta) >= 0);
});

test("empty and single-result extents retain finite, nonzero ranges", () => {
  const historical = record(
    "historical",
    "1922-01-01",
    "1",
    "1",
    "historical-baseline",
  );
  for (const records of [[], [improved], [historical]]) {
    const extent = chartExtent(records);
    assert.ok(Number.isFinite(extent.start));
    assert.ok(Number.isFinite(extent.end));
    assert.ok(extent.end > extent.start);
    assert.ok(cmp(extent.low, extent.high) < 0);
    for (const result of records) {
      assert.ok(extent.start < Date.parse(result.timeline_at));
      assert.ok(extent.end > Date.parse(result.timeline_at));
      assert.ok(cmp(extent.low, result.theta) < 0);
      assert.ok(cmp(extent.high, result.theta) > 0);
    }
  }
});
